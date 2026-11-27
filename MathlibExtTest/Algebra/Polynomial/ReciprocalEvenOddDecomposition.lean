/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import MathlibExt.Algebra.Polynomial.ReciprocalEvenOddDecomposition

/-! # Tests for even–odd decomposition of reciprocal integer polynomials -/

open Polynomial MathlibExt.Algebra.PalindromicZeroOneWanted

-- The third cyclotomic polynomial has `k = l = 1`, so its odd part is constant.
example : ∃! he : ℤ[X], ∃! ho : ℤ[X], ∃! l : ℕ,
    IsReciprocalPoly he ∧ IsReciprocalPoly ho ∧ Odd l ∧ 0 < l ∧
      he.natDegree = 1 ∧ ho.natDegree = 1 - l ∧
      cyclotomic 3 ℤ = he.comp (X ^ 2) + X ^ l * ho.comp (X ^ 2) ∧
      he.eval 0 * ho.eval 0 ≠ 0 := by
  have hdeg : (cyclotomic 3 ℤ).natDegree = 2 * 1 := by
    rw [natDegree_cyclotomic, Nat.totient_prime Nat.prime_three]
  refine existsUnique_evenOdd_reciprocal _ 1 (cyclotomic.irreducible (by decide)) ?_ hdeg ?_
  · apply (isReciprocalPoly_iff _).mpr
    ext n
    rw [coeff_reverse, hdeg]
    by_cases hn : n ≤ 2 * 1
    · rw [revAt_le hn, cyclotomic_three]
      interval_cases n <;> simp [coeff_X_pow, coeff_X, coeff_one]
    · rw [revAt_eq_self_of_lt (lt_of_not_ge hn)]
  · rintro ⟨g, hg⟩
    have hc := congrArg (fun p : ℤ[X] => p.coeff 1) hg
    rw [cyclotomic_three, ← expand_eq_comp_X_pow, coeff_expand two_pos] at hc
    simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one] at hc
    norm_num at hc

example : cyclotomic 3 ℤ = (X + 1 : ℤ[X]).comp (X ^ 2) + X ^ 1 * (1 : ℤ[X]).comp (X ^ 2) := by
  rw [cyclotomic_three]
  simp only [add_comp, one_comp, X_comp, pow_one, mul_one]
  ac_rfl
