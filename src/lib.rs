#![no_std]

use num_integer::Average;
use num_traits::{Bounded, CheckedAdd, CheckedMul, CheckedSub, Unsigned};

pub trait Predicate<T> {
    fn check(&self, index: &T) -> bool;
    fn first_index(&self) -> Option<T>;
    fn last_index_exclusive(&self) -> Option<T>;
}

impl<T, F> Predicate<T> for F
where
    F: Fn(&T) -> bool,
{
    fn check(&self, index: &T) -> bool {
        self(index)
    }

    fn first_index(&self) -> Option<T> {
        None
    }

    fn last_index_exclusive(&self) -> Option<T> {
        None
    }
}

impl Predicate<usize> for &[bool] {
    fn check(&self, index: &usize) -> bool {
        self[*index]
    }

    fn first_index(&self) -> Option<usize> {
        Some(0)
    }

    fn last_index_exclusive(&self) -> Option<usize> {
        Some((*self).len())
    }
}

/// Returns an inclusive range `[a, b]` such that the smallest `i` where
/// `f(i) = false` lies in `[a, b]`.
///
/// `b` is in `[0, 1, 2, 4, 8, 16, ...]`.
///
/// Returns `None` if no such `i` exists.
///
/// Will never return if `T` has no upper bound and no `f(i) = false` can be
/// found.
// TODO: Change `Unsigned` bound to `LowerBounded` when
// https://github.com/rust-num/num-bigint/pull/330 is merged
pub fn exponential_search<T: Unsigned + CheckedMul + PartialOrd>(
    f: impl Predicate<T>,
) -> Option<(T, T)> {
    let len = f.last_index_exclusive();

    if len.as_ref().is_some_and(|n| n.is_zero()) {
        return None;
    }

    if !f.check(&T::zero()) {
        return Some((T::zero(), T::zero()));
    }

    let two = T::one() + T::one();

    let mut prev_i = T::zero();
    let mut i = T::one();
    loop {
        if len.as_ref().is_some_and(|n| &i >= n) {
            return None;
        }

        if !f.check(&i) {
            return Some((prev_i + T::one(), i));
        }

        let next_i = i.checked_mul(&two)?;
        prev_i = i;
        i = next_i;
    }
}

/// Returns the smallest `i` in `[lo, hi]` where `f(i) = false`.
pub fn binary_search_range<T: Average + PartialOrd + Clone + CheckedAdd>(
    mut lo: T,
    mut hi: T,
    f: impl Predicate<T>,
) -> Option<T> {
    if hi < lo {
        return None;
    }

    let mut res = None;
    match hi.checked_add(&T::one()) {
        None => {
            if f.check(&hi) {
                return None;
            } else {
                res = Some(hi.clone());
            }
        }
        Some(new_hi) => hi = new_hi,
    }

    while lo < hi {
        let mid = lo.average_floor(&hi);

        if f.check(&mid) {
            lo = mid + T::one();
        } else {
            res = Some(mid.clone());
            hi = mid;
        }
    }

    res
}

/// Returns the smallest `index` where `f(i) = false`.
pub fn binary_search<T: Average + PartialOrd + Clone + Bounded + CheckedAdd + CheckedSub>(
    f: impl Predicate<T>,
) -> Option<T> {
    let hi = match f.last_index_exclusive() {
        Some(v) => v.checked_sub(&T::one())?,
        None => T::max_value(),
    };

    binary_search_range(f.first_index().unwrap_or_else(T::min_value), hi, f)
}

/// Combines exponential and binary search.
///
/// Unlike `binary_search` this doesn't require `T` to be `Bounded`.
pub fn combined_search<P, T>(f: P) -> Option<T>
where
    T: Unsigned + PartialOrd + CheckedMul + Average + PartialOrd + Clone + CheckedAdd,
    P: Predicate<T>,
    for<'a> &'a P: Predicate<T>,
{
    let (lo, hi) = exponential_search(&f)?;
    binary_search_range(lo, hi, f)
}

#[cfg(test)]
mod test {
    extern crate std;
    use std::{prelude::rust_2024::*, vec};

    use num_bigint::BigUint;
    use num_traits::One;

    use super::*;

    #[test]
    fn test_exp() {
        assert_eq!(exponential_search(|_: &usize| false), Some((0, 0)));
        assert_eq!(exponential_search(|&i: &usize| i == 0), Some((1, 1)));
        assert_eq!(exponential_search(|&i: &usize| i <= 1), Some((2, 2)));
        assert_eq!(exponential_search(|&i: &usize| i <= 2), Some((3, 4)));
        assert_eq!(exponential_search(|&i: &usize| i <= 3), Some((3, 4)));
        assert_eq!(exponential_search(|&i: &usize| i <= 4), Some((5, 8)));
        assert_eq!(exponential_search(|&i: &usize| i <= 7), Some((5, 8)));
        assert_eq!(exponential_search(|&i: &usize| i <= 8), Some((9, 16)));
        assert_eq!(exponential_search(|&i: &usize| i != usize::MAX), None);
        assert_eq!(exponential_search(|_: &usize| true), None);

        let two = BigUint::from(2u8);
        let v = two.pow(1024);
        assert_eq!(
            exponential_search(|i: &BigUint| i <= &v),
            Some((two.pow(1024) + 1u8, two.pow(1025)))
        );

        assert_eq!(exponential_search(&[][..]), None);
        assert_eq!(exponential_search(&[true][..]), None);
        assert_eq!(exponential_search(&[false][..]), Some((0, 0)));
        assert_eq!(exponential_search(&[true, true][..]), None);
        assert_eq!(exponential_search(&[true, false][..]), Some((1, 1)));
        assert_eq!(exponential_search(&[true, true, true][..]), None);
        assert_eq!(exponential_search(&[true, true, false][..]), Some((2, 2)));
        assert_eq!(exponential_search(&[true, true, true, true][..]), None);
        assert_eq!(exponential_search(&[true, true, true, false][..]), None);
        assert_eq!(
            exponential_search(&[true, true, true, true, true][..]),
            None
        );
        assert_eq!(
            exponential_search(&[true, true, true, true, false][..]),
            Some((3, 4))
        );
    }

    #[test]
    fn test_binary() {
        assert_eq!(binary_search(&[][..]), None);

        let mut v = vec![];
        for _ in 0..10 {
            v.push(false);
            assert_eq!(binary_search(v.as_slice()), Some(v.len() - 1));
            v.pop().unwrap();

            assert_eq!(binary_search(v.as_slice()), None);
            v.push(true);
        }
    }

    #[test]
    fn test_binary_range() {
        assert_eq!(binary_search_range(0, 0, |_: &usize| false), Some(0));
        assert_eq!(binary_search_range(0, 0, |_: &usize| true), None);
        assert_eq!(
            binary_search_range(usize::MAX, usize::MAX, |_: &usize| false),
            Some(usize::MAX)
        );
        assert_eq!(
            binary_search_range(usize::MAX, usize::MAX, |_: &usize| true),
            None
        );
        assert_eq!(
            binary_search_range(0, usize::MAX, |_: &usize| false),
            Some(0)
        );
        assert_eq!(binary_search_range(0, usize::MAX, |_: &usize| true), None);
        assert_eq!(
            binary_search_range(usize::MAX - 1, usize::MAX, |_: &usize| false),
            Some(usize::MAX - 1)
        );
        assert_eq!(
            binary_search_range(usize::MAX - 1, usize::MAX, |_: &usize| true),
            None
        );

        for i in 0..10 {
            assert_eq!(binary_search_range(0, i, |_: &usize| false), Some(0));
            assert_eq!(binary_search_range(0, i, |_: &usize| true), None);
        }

        for hi in 0..10 {
            for res in 0..=hi {
                assert_eq!(
                    binary_search_range(0, hi, |&i: &usize| i < res),
                    Some(res),
                    "hi={hi}, res={res}"
                );
            }
        }
    }

    #[test]
    fn test_combined() {
        assert_eq!(
            combined_search(|v: &BigUint| v <= &BigUint::from(123u8)),
            Some(124u8.into())
        );
        assert_eq!(
            combined_search(|v: &BigUint| v <= &BigUint::from(2u8).pow(1024)),
            Some(BigUint::from(2u8).pow(1024) + BigUint::one())
        );
    }
}
