/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlternatingHyperharmonicTypeIIISquarefree
import Mathlib.Tactic.NormNum

/-! # Tests for type III alternating hyperharmonic power sums over squarefree numbers -/

open MetaMathlibExt Asymptotics Filter Finset

-- Both levels of type III summation alternate: `H_2^{(1,2,3)} = H̄_1 - H̄_2 = 1 / 2`, the value
-- `∑_{m ≤ 1} (2m)⁻¹` of the even-index formula.
example : signedIteratedPartialSum true (alternatingGeneralizedHarmonic 1) 2 2 = 1 / 2 := by
  norm_num [signedIteratedPartialSum, alternatingGeneralizedHarmonic, Finset.sum_Icc_succ_top]

-- For `k = 1` the weights are the primes and `ζ̄(1) = log 2`: with all parameters equal to one,
-- `∑_{l ≤ x} p_l H_l^{(1,3,3)} ~ log 2 · x³ log x / 6`.
example : (fun x : ℕ => ∑ l ∈ Icc 1 x,
      (Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = 1) (l - 1) : ℝ) *
        signedIteratedPartialSum true (alternatingGeneralizedHarmonic 1) 3 l) ~[atTop]
    fun x : ℕ => Real.log 2 * (x : ℝ) ^ 3 * Real.log x / 6 := by
  have h := (sum_squarefreeKPrime_pow_mul_alternatingHyperharmonic_typeIII_isEquivalent
    (α := 1) (m := 1) (k := 1) (p := 1) (y := 1) (q := 2) le_rfl le_rfl le_rfl le_rfl le_rfl
    (by norm_num)).1
  refine (h.congr_left (Eventually.of_forall fun x => ?_)).congr_right
    (Eventually.of_forall fun x => ?_)
  · simp
  · norm_num

-- Restricting the same sum to `p_l ≤ x` divides its asymptotic by `(log x) ^ 3`:
-- `∑_{l ≤ x, p_l ≤ x} p_l H_l^{(1,3,3)} ~ log 2 · x³ / (6 (log x)²)`.
example : (fun x : ℕ => ∑ l ∈ (Icc 1 x).filter
      (fun l => Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = 1) (l - 1) ≤ x),
      (Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = 1) (l - 1) : ℝ) *
        signedIteratedPartialSum true (alternatingGeneralizedHarmonic 1) 3 l) ~[atTop]
    fun x : ℕ => Real.log 2 * (x : ℝ) ^ 3 / (6 * Real.log x ^ 2) := by
  have h := (sum_squarefreeKPrime_pow_mul_alternatingHyperharmonic_typeIII_isEquivalent
    (α := 1) (m := 1) (k := 1) (p := 1) (y := 1) (q := 2) le_rfl le_rfl le_rfl le_rfl le_rfl
    (by norm_num)).2.1
  refine (h.congr_left (Eventually.of_forall fun x => ?_)).congr_right
    (Eventually.of_forall fun x => ?_)
  · simp
  · norm_num
