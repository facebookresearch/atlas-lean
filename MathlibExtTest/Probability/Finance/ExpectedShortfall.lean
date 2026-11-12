/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.ExpectedShortfall
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! # Tests for `MathlibExt.Probability.Finance.ExpectedShortfall` -/

open MeasureTheory ProbabilityTheory Set MathlibExt.Probability.Finance.ExpectedShortfall

namespace MathlibExtTest.ExpectedShortfall

theorem ex_hp : ∀ ω : Fin 2, 0 ≤ (![1/2, 1/2] : Fin 2 → ℝ) ω := by
  intro i
  fin_cases i <;> norm_num

theorem ex_hp1 : ∑ ω : Fin 2, (![1/2, 1/2] : Fin 2 → ℝ) ω = 1 := by
  rw [Fin.sum_univ_two]; norm_num

/-- Value-at-risk of the atom example is `0`. -/
theorem ex_VaR : cdfQuantile (lossLaw ![1/2, 1/2] ![0, 1]) (1/2) = 0 := by
  have hmem : (1/2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  unfold ProbabilityTheory.cdfQuantile
  simp only [hmem, ite_true]
  have hset : {x : ℝ | (1/2 : ℝ) ≤ cdf (lossLaw ![1/2, 1/2] ![0, 1]) x} = Ici 0 := by
    ext x
    show ((1/2 : ℝ) ≤ cdf (lossLaw ![1/2, 1/2] ![0, 1]) x) ↔ x ∈ Ici (0 : ℝ)
    rw [mem_Ici]
    constructor
    · intro h
      by_contra hcon
      push Not at hcon
      have hempty : Finset.univ.filter (fun ω : Fin 2 => ![0, 1] ω ≤ x) = ∅ := by
        apply Finset.filter_false_of_mem
        intro i _
        fin_cases i
        · show ¬ (0 : ℝ) ≤ x
          exact not_le.mpr hcon
        · show ¬ (1 : ℝ) ≤ x
          exact not_le.mpr (lt_trans hcon (by norm_num))
      rw [cdf_lossLaw_eq ex_hp ex_hp1] at h
      rw [hempty, Finset.sum_empty] at h
      norm_num at h
    · intro h
      rw [cdf_lossLaw_eq ex_hp ex_hp1]
      have hsub : ({0} : Finset (Fin 2)) ⊆
          Finset.univ.filter (fun ω : Fin 2 => ![0, 1] ω ≤ x) := by
        intro i hi
        simp only [Finset.mem_singleton] at hi
        subst hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        show (0 : ℝ) ≤ x
        exact h
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => ex_hp i)
      simp only [Finset.sum_singleton] at hle
      exact hle
  rw [hset]
  exact csInf_Ici

/-- Atom at the quantile: expected shortfall is `1` (while `VaR = 0`). -/
theorem ex_es_atom : expectedShortfall ![1/2, 1/2] (1/2) ![0, 1] = 1 := by
  rw [expectedShortfall_eq_valueAtRisk_add ex_hp ex_hp1 (by norm_num) (by norm_num) _,
    ex_VaR, Fin.sum_univ_two]
  norm_num

/-- The naive conditional tail mean is `1/2`, unlike the expected shortfall. -/
theorem ex_naive : (∑ ω, ![1/2, 1/2] ω * ![0, 1] ω) / (∑ ω, ![1/2, 1/2] ω) = 1/2 := by
  simp only [Fin.sum_univ_two]
  norm_num

/-- The quantile form agrees on the atom example. -/
theorem ex_qes_atom : quantileExpectedShortfall ![1/2, 1/2] (1/2) ![0, 1] = 1 := by
  rw [quantileExpectedShortfall_eq_expectedShortfall ex_hp ex_hp1 (by norm_num) (by norm_num) _]
  exact ex_es_atom

/-- Subadditivity instance on the two-point space. -/
theorem ex_subadd : expectedShortfall ![1/2, 1/2] (1/2) (![0, 1] + ![1, 0]) ≤
    expectedShortfall ![1/2, 1/2] (1/2) ![0, 1] +
      expectedShortfall ![1/2, 1/2] (1/2) ![1, 0] :=
  expectedShortfall_add_le ex_hp ex_hp1 (by norm_num) (by norm_num) _ _

end MathlibExtTest.ExpectedShortfall
