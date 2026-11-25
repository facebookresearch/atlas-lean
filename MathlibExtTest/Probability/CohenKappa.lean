/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.CohenKappa
import Mathlib.Tactic.NormNum

open WantedExt.Biology.StatisticalGenetics.CohenKappaWanted

/-- Two categories with equal mass and no disagreement. -/
private noncomputable def balancedAgreement (i j : Fin 2) : ℝ :=
  if i = j then 1 / 2 else 0

private theorem balancedAgreement_isTable : IsTable balancedAgreement := by
  constructor
  · intro i j
    by_cases h : i = j <;> norm_num [balancedAgreement, h]
  · norm_num [balancedAgreement, Fin.sum_univ_two]

example : kappa balancedAgreement = 1 := by
  have he : chance balancedAgreement < 1 := by
    norm_num [chance, rowMargin, colMargin, balancedAgreement, Fin.sum_univ_two]
  apply (kappa_eq_one_iff (P := balancedAgreement) (hP := balancedAgreement_isTable) (he := he)).2
  norm_num [observed, balancedAgreement, Fin.sum_univ_two]

-- With just one category, observed agreement is perfect but the chance term is also one.
example : chance (fun _ _ : Fin 1 ↦ 1) = 1 ∧
    observed (fun _ _ : Fin 1 ↦ 1) = 1 ∧ kappa (fun _ _ : Fin 1 ↦ 1) = 0 := by
  norm_num [kappa, observed, chance, rowMargin, colMargin, Fin.sum_univ_one]
