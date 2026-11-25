/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosGrahamCovering
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Tests for `MathlibExt.NumberTheory.ErdosGrahamCovering` -/

namespace MathlibExtTest.ErdosGrahamCovering

open MathlibExt.NumberTheory.ErdosGrahamCoveringWanted

-- Test section: the bound is attained. The classes `0 (mod 2)`, `1 (mod 4)` and `3 (mod 4)`
-- cover the integers, so the hypotheses can hold, and `1/2 + 1/4 + 1/4 = 1`. The modulus `4`
-- appears twice and is counted twice.
example : (1 : ℚ) ≤ ∑ i, (1 : ℚ) / ((![2, 4, 4] : Fin 3 → ℕ) i : ℚ) ∧
    ∑ i, (1 : ℚ) / ((![2, 4, 4] : Fin 3 → ℕ) i : ℚ) = 1 := by
  have hcov : Int.IsCoveringSystem (Int.indexedCoveringClasses ![2, 4, 4] ![0, 1, 3]) := by
    rw [Int.indexedCoveringClasses_isCoveringSystem_iff]
    intro z
    rcases (by omega : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3) with h | h | h | h
    · exact ⟨0, by simp [Int.ModEq]; omega⟩
    · exact ⟨1, by simp [Int.ModEq]; omega⟩
    · exact ⟨0, by simp [Int.ModEq]; omega⟩
    · exact ⟨2, by simp [Int.ModEq]; omega⟩
  exact ⟨one_le_sum_inv_moduli _ _ (by decide) hcov, by norm_num [Fin.sum_univ_three]⟩

-- Test section: obstructions. No residues make `2`, `3`, `7` the moduli of a covering system,
-- since `1/2 + 1/3 + 1/7 = 41/42 < 1`.
example (a : Fin 3 → ℤ) : ¬ Int.IsCoveringSystem (Int.indexedCoveringClasses ![2, 3, 7] a) := by
  intro h
  have h1 := one_le_sum_inv_moduli ![2, 3, 7] a (by decide) h
  norm_num [Fin.sum_univ_three] at h1

-- A covering system with `t` classes has a modulus at most `t`: if every modulus exceeds `t`,
-- the reciprocal sum is at most `t / (t + 1) < 1`. For `t = 0` this says the empty family does
-- not cover.
example {t : ℕ} (d : Fin t → ℕ) (a : Fin t → ℤ) (hd : ∀ i, t < d i) :
    ¬ Int.IsCoveringSystem (Int.indexedCoveringClasses d a) := by
  intro h
  have h1 := one_le_sum_inv_moduli d a (fun i => (Nat.zero_le t).trans_lt (hd i)) h
  have h2 : ∑ i, (1 : ℚ) / (d i : ℚ) ≤ ∑ _i : Fin t, (1 : ℚ) / ((t : ℚ) + 1) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hti : (t : ℚ) + 1 ≤ d i := by exact_mod_cast hd i
    exact one_div_le_one_div_of_le (by positivity) hti
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div] at h2
  have h3 : (t : ℚ) / ((t : ℚ) + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  linarith

-- Edge case: the single class `0 (mod 1)` covers the integers, with reciprocal sum exactly `1`.
example : (1 : ℚ) ≤ ∑ i, (1 : ℚ) / ((![1] : Fin 1 → ℕ) i : ℚ) :=
  one_le_sum_inv_moduli ![1] ![0] (by decide) fun z =>
    ⟨(0, 1), Finset.mem_image_of_mem _ (Finset.mem_univ 0), Int.modEq_one⟩

end MathlibExtTest.ErdosGrahamCovering
