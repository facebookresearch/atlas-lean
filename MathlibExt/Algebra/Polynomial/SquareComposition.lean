/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Expand

/-!
# Reflection-invariant polynomials and square substitution

Over a characteristic-zero domain, a polynomial invariant under `X ↦ -X`
is a polynomial in `X ^ 2`.

## References

* The proof was originally in `MathlibExt.Algebra.Polynomial.ZeroOneSquareComposition`
  and is now shared with the Faulhaber development.
-/

namespace Polynomial

/-- Over a characteristic-zero domain, a polynomial fixed by `X ↦ -X` has only even powers.
Thus contracting by two and expanding again recovers the polynomial. -/
public theorem expand_contract_of_comp_neg_X_eq {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] {p : R[X]} (hp : p.comp (-X) = p) : expand R 2 (p.contract 2) = p := by
  ext n
  rw [coeff_expand (by decide : 0 < 2), coeff_contract two_ne_zero]
  split_ifs with hn
  · rw [Nat.div_mul_cancel hn]
  · have hodd : Odd n := Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp hn)
    have h := congrArg (fun q : R[X] => q.coeff n) hp
    rw [show (-X : R[X]) = C (-1) * X by simp, comp_C_mul_X_coeff,
      hodd.neg_one_pow, mul_neg_one] at h
    have hzero : (2 : R) * p.coeff n = 0 := by
      simpa [two_mul] using congrArg (fun r : R => r + p.coeff n) h.symm
    exact ((mul_eq_zero.mp hzero).resolve_left two_ne_zero).symm

end Polynomial
