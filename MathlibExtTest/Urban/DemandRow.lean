/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

import MathlibExt.Urban.DemandRow

/-!
# Demand row checks

Focused checks for `MathlibExt.Urban.DemandRow`: origin total `10` with
weights `![1, 3]` over `Fin 2` gives row `(5 / 2, 15 / 2)` with total
`10`.

These are elaboration and non-vacuity checks, not new results.
-/

open UrbanDemand

/-- Row entries and total at the witness weights. -/
example : normalizedDemand (10 : ℝ) ![1, 3] Finset.univ 0 = 5 / 2
    ∧ normalizedDemand (10 : ℝ) ![1, 3] Finset.univ 1 = 15 / 2
    ∧ ∑ i : Fin 2, normalizedDemand (10 : ℝ) ![1, 3] Finset.univ i = 10 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [normalizedDemand, Fin.sum_univ_two]
  · norm_num [normalizedDemand, Fin.sum_univ_two]
  · exact normalizedDemand_sum (10 : ℝ) ![1, 3] Finset.univ (by norm_num)
      (by intro i _; fin_cases i <;> simp) (by norm_num [Fin.sum_univ_two])

/-- Proper-subset destinations: a negative weight outside `s` is
irrelevant to the row over `s = {0}`. -/
example : (0 : ℝ) ≤ normalizedDemand (10 : ℝ) ![1, -1] ({0} : Finset (Fin 2)) 0
    ∧ ∑ i ∈ ({0} : Finset (Fin 2)), normalizedDemand (10 : ℝ) ![1, -1] {0} i = 10 := by
  refine ⟨?_, ?_⟩
  · exact normalizedDemand_nonneg _ _ _ (by norm_num)
      (by intro i hi; simp at hi; simp [hi]) (by simp) (by simp)
  · exact normalizedDemand_sum _ _ _ (by norm_num)
      (by intro i hi; simp at hi; simp [hi]) (by simp)
