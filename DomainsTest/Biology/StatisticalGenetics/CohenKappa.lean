/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.StatisticalGenetics.CohenKappa
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace DomainsTest.Biology.StatisticalGenetics.CohenKappa

open WantedExt.Biology.StatisticalGenetics.CohenKappaWanted

private noncomputable def unequalMargins : Fin 2 → Fin 2 → ℝ :=
  fun i _ => if i = 0 then 3 / 8 else 1 / 8

private lemma unequalMargins_isTable : IsTable unequalMargins := by
  constructor
  · intro i j
    fin_cases i <;> norm_num [unequalMargins]
  · norm_num [unequalMargins, Fin.sum_univ_two]

example : kappa unequalMargins = 0 ∧ kappaMax unequalMargins = 1 / 2 := by
  norm_num [kappa, kappaMax, observed, chance, rowMargin, colMargin,
    unequalMargins, Fin.sum_univ_two]

example (Q : Fin 2 → Fin 2 → ℝ) (hQ : IsTable Q)
    (hr : ∀ i, rowMargin Q i = rowMargin unequalMargins i)
    (hc : ∀ j, colMargin Q j = colMargin unequalMargins j) : kappa Q ≤ 1 / 2 := by
  have h := (kappa_le_kappaMax unequalMargins unequalMargins_isTable
    (by norm_num [chance, rowMargin, colMargin, unequalMargins, Fin.sum_univ_two])).2.1
      Q hQ hr hc
  norm_num [kappaMax, chance, rowMargin, colMargin, unequalMargins, Fin.sum_univ_two] at h
  exact h

lemma unequal_margins_attainment :
    ∃ Q : Fin 2 → Fin 2 → ℝ, IsTable Q ∧ rowMargin Q 0 = 3 / 4 ∧
      rowMargin Q 1 = 1 / 4 ∧ (∀ j, colMargin Q j = 1 / 2) ∧ kappa Q = 1 / 2 := by
  obtain ⟨Q, hQ, hr, hc, hk⟩ :=
    (kappa_le_kappaMax unequalMargins unequalMargins_isTable
      (by norm_num [chance, rowMargin, colMargin, unequalMargins, Fin.sum_univ_two])).2.2
  refine ⟨Q, hQ, ?_, ?_, ?_, ?_⟩
  · rw [hr]
    norm_num [rowMargin, unequalMargins, Fin.sum_univ_two]
  · rw [hr]
    norm_num [rowMargin, unequalMargins, Fin.sum_univ_two]
  · intro j
    rw [hc]
    norm_num [colMargin, unequalMargins, Fin.sum_univ_two]
  · rw [hk]
    norm_num [kappaMax, chance, rowMargin, colMargin, unequalMargins, Fin.sum_univ_two]

lemma equal_margins_attainment :
    ∃ Q : Fin 2 → Fin 2 → ℝ, IsTable Q ∧ (∀ i, rowMargin Q i = 1 / 2) ∧
      (∀ j, colMargin Q j = 1 / 2) ∧ kappa Q = 1 := by
  let P : Fin 2 → Fin 2 → ℝ := fun _ _ => 1 / 4
  have hP : IsTable P := by
    constructor
    · intro i j
      norm_num [P]
    · norm_num [P, Fin.sum_univ_two]
  obtain ⟨Q, hQ, hr, hc, hk⟩ := (kappa_le_kappaMax P hP
    (by norm_num [chance, rowMargin, colMargin, P, Fin.sum_univ_two])).2.2
  refine ⟨Q, hQ, ?_, ?_, ?_⟩
  · intro i
    rw [hr]
    norm_num [rowMargin, P, Fin.sum_univ_two]
  · intro j
    rw [hc]
    norm_num [colMargin, P, Fin.sum_univ_two]
  · rw [hk]
    norm_num [kappaMax, chance, rowMargin, colMargin, P, Fin.sum_univ_two]

#check @WantedExt.Biology.StatisticalGenetics.CohenKappaWanted.kappa_le_kappaMax
#print axioms WantedExt.Biology.StatisticalGenetics.CohenKappaWanted.kappa_le_kappaMax
#print axioms unequal_margins_attainment
#print axioms equal_margins_attainment

end DomainsTest.Biology.StatisticalGenetics.CohenKappa
