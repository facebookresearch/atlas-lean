/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.InformationTheory.JensenShannonOneHot
import Mathlib.Tactic.NormNum

/-! # Tests for Jensen–Shannon divergence and one-hot specificity -/

open InformationTheory Real
open scoped ENNReal NNReal

private noncomputable def fair : PMF Bool :=
  PMF.ofFintype (fun _ => ((1 / 2 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj, add_halves])

-- A point mass compared with itself has zero divergence; disjoint point masses give one bit.
example : jensenShannonBits (PMF.pure true) (PMF.pure true) = 0 := by
  simp [jensenShannonBits_pure]

example : jensenShannonBits (PMF.pure false) (PMF.pure true) = 1 := by
  simp [jensenShannonBits_pure]

-- Comparing the fair coin to a point mass exercises both finite KL terms in the interior.
example : jensenShannonBits fair (PMF.pure true) =
    1 + ((1 / 2) * log (1 / 2) - (3 / 2) * log (3 / 2)) / (2 * log 2) := by
  rw [jensenShannonBits_pure]
  norm_num [fair, oneHotJensenShannon, negMulLog_eq_neg, sub_eq_add_neg, add_comm]

-- The score ranks interior masses and puts the unit-mass score strictly above them.
example : oneHotSpecificity (1 / 4) < oneHotSpecificity (1 / 2) := by
  apply strictMonoOn_oneHotSpecificity <;> norm_num

example : oneHotSpecificity (1 / 2) < oneHotSpecificity 1 := by
  apply strictMonoOn_oneHotSpecificity <;> norm_num

example : oneHotSpecificity 1 = ⊤ :=
  (oneHotSpecificity_eq_top_iff (by simp)).2 rfl

example : oneHotSpecificity (1 / 2) ≠ ⊤ := by
  have h : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  simpa using (oneHotSpecificity_eq_top_iff h).not
