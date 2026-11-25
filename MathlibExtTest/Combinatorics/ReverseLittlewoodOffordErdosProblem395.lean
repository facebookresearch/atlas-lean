/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ReverseLittlewoodOffordErdosProblem395
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Tests for `MathlibExt.Combinatorics.ReverseLittlewoodOffordErdosProblem395` -/

namespace MathlibExtTest.ReverseLittlewoodOffordErdosProblem395

open MathlibExt.Combinatorics.ReverseLittlewoodOffordErdosProblem395Wanted

-- Test section: `smallSignedSumCount` on small families.

-- With one unit vector, both signed sums `±1` are short.
example : smallSignedSumCount ![(1 : ℂ)] = 2 := by
  have h : {ε : Fin 1 → Bool |
      ‖∑ i, (if ε i then (1 : ℂ) else -1) * ![(1 : ℂ)] i‖ ≤ Real.sqrt 2} = Set.univ := by
    ext ε
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, Fin.sum_univ_one,
      Matrix.cons_val_zero, mul_one]
    cases ε 0 <;> simp [Complex.norm_def, Real.one_le_sqrt]
  rw [smallSignedSumCount, h, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun]
  simp

-- For `1` and `i`, all four signed sums have norm exactly `√2`; the bound is not strict.
example : smallSignedSumCount ![(1 : ℂ), Complex.I] = 4 := by
  have h : {ε : Fin 2 → Bool |
      ‖∑ i, (if ε i then (1 : ℂ) else -1) * ![(1 : ℂ), Complex.I] i‖ ≤ Real.sqrt 2}
      = Set.univ := by
    ext ε
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    cases ε 0 <;> cases ε 1 <;> simp [Complex.norm_def, Complex.normSq_apply] <;> norm_num
  rw [smallSignedSumCount, h, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun]
  simp

-- For two equal unit vectors, only the two sign vectors with opposite signs give a short sum:
-- the sums `±2` are too long.
example : smallSignedSumCount ![(1 : ℂ), 1] = 2 := by
  have h : {ε : Fin 2 → Bool |
      ‖∑ i, (if ε i then (1 : ℂ) else -1) * ![(1 : ℂ), 1] i‖ ≤ Real.sqrt 2}
      = ↑(Finset.univ.filter fun ε : Fin 2 → Bool => ε 0 ≠ ε 1) := by
    ext ε
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    rw [Fin.sum_univ_two]
    cases ε 0 <;> cases ε 1 <;> norm_num
  rw [smallSignedSumCount, h, Set.ncard_coe_finset]
  decide

-- Test section: consequences of the main theorem.

-- Every nonempty family of unit vectors has a sign vector with a short signed sum.
example (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    0 < smallSignedSumCount z := by
  obtain ⟨c, hc, h⟩ := reverseLittlewoodOffordSqrtTwo_holds
  have h1 := h n hn z hz
  by_contra h0
  rw [Nat.not_lt, Nat.le_zero] at h0
  rw [h0, Nat.cast_zero, zero_div] at h1
  have : 0 < c / n := by positivity
  linarith

-- The bound applies uniformly to the constant families `(1, …, 1)`.
example : ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 0 < m →
    c / m ≤ (smallSignedSumCount (fun _ : Fin m => (1 : ℂ)) : ℝ) / 2 ^ m := by
  obtain ⟨c, hc, h⟩ := reverseLittlewoodOffordSqrtTwo_holds
  exact ⟨c, hc, fun m hm => h m hm (fun _ => 1) fun _ => by simp [Complex.norm_def]⟩

end MathlibExtTest.ReverseLittlewoodOffordErdosProblem395
