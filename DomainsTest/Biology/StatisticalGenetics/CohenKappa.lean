/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.CohenKappa
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for Cohen's kappa

The uniform `2 × 2` table is the product of its margins, so its kappa is `0`; and on any
independent table the observed agreement equals the chance agreement. The table with rows
`(3/8, 3/8)` and `(1/8, 1/8)` has `κ = 0` and `κ_max = 1/2`; every table with its margins has
`κ ≤ 1/2`, and some table attains it. A table with uniform margins attains `κ = 1`. The table
with rows `(1, 0)` and `(0, 0)` has `p_e = 1`, where `kappaMax` is `0` by the convention
`x / 0 = 0`.
-/

@[expose] public section

open WantedExt.Biology.StatisticalGenetics.CohenKappaWanted

namespace DomainsTest.Biology.StatisticalGenetics.CohenKappa

/-- The uniform `2 × 2` table is a probability table. -/
private lemma isTable_uniform_two : IsTable (fun _ _ : Fin 2 => (1 / 4 : ℝ)) := by
  refine ⟨fun i j => ?_, ?_⟩
  · show (0 : ℝ) ≤ 1 / 4
    norm_num
  · simp only [Fin.sum_univ_two]
    norm_num

/-- The uniform `2 × 2` table is the product of its margins. -/
private lemma independence_two (i j : Fin 2) :
    (fun _ _ : Fin 2 => (1 / 4 : ℝ)) i j =
      rowMargin (fun _ _ : Fin 2 => (1 / 4 : ℝ)) i *
        colMargin (fun _ _ : Fin 2 => (1 / 4 : ℝ)) j := by
  simp only [rowMargin, colMargin, Fin.sum_univ_two]
  norm_num

/-- The uniform `2 × 2` table has chance agreement below `1`. -/
private lemma chance_two : chance (fun _ _ : Fin 2 => (1 / 4 : ℝ)) < 1 := by
  simp only [chance, rowMargin, colMargin, Fin.sum_univ_two]
  norm_num

/-- The uniform `2 × 2` table has kappa `0`. -/
example : kappa (fun _ _ : Fin 2 => (1 / 4 : ℝ)) = 0 :=
  kappa_eq_zero_of_independent _ isTable_uniform_two independence_two chance_two

/-- On an independent table, observed agreement equals chance agreement. -/
example {k : ℕ} (P : Fin k → Fin k → ℝ)
    (hind : ∀ i j, P i j = rowMargin P i * colMargin P j) :
    observed P = chance P := by
  simp only [observed, chance, hind]

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

-- At the boundary `p_e = 1` the denominator of `κ_max` vanishes: the table with rows `(1, 0)` and
-- `(0, 0)` is a joint probability table with `chance = 1`, and `kappaMax` gives `0` by `x / 0 = 0`.
private noncomputable def chanceOne : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 0]]

example : IsTable chanceOne ∧ chance chanceOne = 1 ∧ kappaMax chanceOne = 0 := by
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num [chanceOne]
  · simp only [Fin.sum_univ_two]
    norm_num [chanceOne]
  · simp only [chance, rowMargin, colMargin, Fin.sum_univ_two]
    norm_num [chanceOne]
  · simp only [kappaMax, chance, rowMargin, colMargin, Fin.sum_univ_two]
    norm_num [chanceOne]

#check @WantedExt.Biology.StatisticalGenetics.CohenKappaWanted.kappa_le_kappaMax
#print axioms WantedExt.Biology.StatisticalGenetics.CohenKappaWanted.kappa_le_kappaMax
#print axioms unequal_margins_attainment
#print axioms equal_margins_attainment

end DomainsTest.Biology.StatisticalGenetics.CohenKappa
