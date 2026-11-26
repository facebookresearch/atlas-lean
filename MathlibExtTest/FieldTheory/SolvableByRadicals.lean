/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.SolvableByRadicals

open Polynomial
open MathlibExt.Algebra.SolvableByRadicalsWanted.Algebra

/-- The forward direction handles products and repeated factors, not only irreducibles. -/
example {F : Type*} [Field F] [CharZero F] (a b : F) :
    Group.IsSolvable (((X ^ 2 - C a) ^ 2 * (X - C b)) : F[X]).Gal := by
  have hq : (X ^ 2 - C a).Monic := monic_X_pow_sub_C a (by decide)
  have hp := (hq.pow 2).mul (monic_X_sub_C b)
  apply (solvable_iff_solvableByRad F _ hp.ne_zero).mp
  intro x hx
  simp only [map_mul, map_pow, map_sub, aeval_X, aeval_C, mul_eq_zero, pow_eq_zero_iff two_ne_zero,
    sub_eq_zero] at hx
  rcases hx with h | h
  · exact solvableByRad.rad_mem two_ne_zero (h.symm ▸ (solvableByRad F _).algebraMap_mem a)
  · exact h.symm ▸ (solvableByRad F _).algebraMap_mem b

/-- The converse supplies radical membership for a root that exists in the algebraic closure. -/
example {F : Type*} [Field F] [CharZero F] (a : F) :
    ∃ x : AlgebraicClosure F,
      x ^ 3 = algebraMap F _ a ∧ x ∈ solvableByRad F (AlgebraicClosure F) := by
  let p : F[X] := X ^ 3 - C a
  have hp : p.Monic := monic_X_pow_sub_C a (by decide)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) a)
    (show 0 < (3 : ℕ) by decide)
  have hroot : aeval x p = 0 := by simp [p, hx]
  exact ⟨x, hx,
    (solvable_iff_solvableByRad F p hp.ne_zero).mpr (gal_X_pow_sub_C_isSolvable 3 a) x hroot⟩

/-- The forward direction includes nonzero constants, for which the root condition is vacuous. -/
example {F : Type*} [Field F] [CharZero F] (a : F) (ha : a ≠ 0) :
    Group.IsSolvable (C a).Gal := by
  apply (solvable_iff_solvableByRad F (C a) (C_ne_zero.mpr ha)).mp
  intro x hx
  exact (ha ((algebraMap F (AlgebraicClosure F)).injective (by simpa using hx))).elim
