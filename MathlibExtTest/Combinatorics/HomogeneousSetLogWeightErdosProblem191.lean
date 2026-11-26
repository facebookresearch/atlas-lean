/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.HomogeneousSetLogWeightErdosProblem191
import Mathlib.Tactic.Positivity

/-!
# A monochromatic pair from the logarithmic weight bound

Each vertex in `Finset.Icc 2 n` has weight at most `1 / Real.log 2`, so a monochromatic set
whose weight exceeds this threshold contains at least two vertices.
-/

open Filter MathlibExt.Combinatorics.HomogeneousSetLogWeightErdosProblem191Wanted

example : ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph ℕ, ∃ X : Finset ℕ,
    X ⊆ Finset.Icc 2 n ∧ (G.IsClique (X : Set ℕ) ∨ G.IsIndepSet (X : Set ℕ)) ∧
      1 < X.card := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < 1 / Real.log 2 + 1 := by positivity
  filter_upwards [homogeneousSetLargeLogWeight_holds _ hC] with n hn G
  obtain ⟨X, hX, hmono, hw⟩ := hn G
  refine ⟨X, hX, hmono, ?_⟩
  by_contra! hcard
  have hle : ∑ x ∈ X, 1 / Real.log x ≤ 1 / Real.log 2 := by
    calc
      ∑ x ∈ X, 1 / Real.log x ≤ ∑ _x ∈ X, 1 / Real.log 2 := by
        apply Finset.sum_le_sum
        intro x hx
        have hx₂ : (2 : ℝ) ≤ x := by exact_mod_cast (Finset.mem_Icc.mp (hX hx)).1
        exact one_div_le_one_div_of_le hlog (Real.log_le_log (by norm_num) hx₂)
      _ = (X.card : ℝ) * (1 / Real.log 2) := by simp [nsmul_eq_mul]
      _ ≤ 1 / Real.log 2 := by
        have hcard' : (X.card : ℝ) ≤ 1 := by exact_mod_cast hcard
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hcard' (by positivity : 0 ≤ 1 / Real.log 2)
  exact (not_lt_of_ge (hw.trans hle)) (lt_add_one _)
