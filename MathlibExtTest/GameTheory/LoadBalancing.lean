/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.LoadBalancing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum

@[expose] public section

open Finset MathlibExt.GameTheory.LoadBalancing

namespace MathlibExtTest.GameTheory.LoadBalancing

/-- Vöcking's example (*Algorithmic Game Theory*, Section 20.1.2): two large tasks of weight `2`
and two small tasks of weight `1`. -/
def w : Fin 4 → ℝ := ![2, 2, 1, 1]

/-- The equilibrium of the example: both large tasks on machine `0`, both small on machine `1`
(loads `4` and `2`). -/
def A : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- The optimal assignment of the example: one large and one small task per machine (loads `3`
and `3`). -/
def B : Fin 4 → Fin 2 := ![0, 1, 0, 1]

lemma load_A_zero : load w A 0 = 4 := by
  rw [load, sum_filter, Fin.sum_univ_four]; norm_num [w, A]

lemma load_A_one : load w A 1 = 2 := by
  rw [load, sum_filter, Fin.sum_univ_four]; norm_num [w, A]

lemma load_A : load w A = ![4, 2] := by
  funext j; fin_cases j
  · exact load_A_zero
  · exact load_A_one

lemma load_B (j : Fin 2) : load w B j = 3 := by
  fin_cases j <;> (rw [load, sum_filter, Fin.sum_univ_four]; norm_num [w, B])

/-- Non-vacuity: `A` is a pure Nash equilibrium (no task gains by moving). -/
theorem isPureNash_A : IsPureNash w A := by
  intro i k hk
  rw [load_A]
  fin_cases i <;> fin_cases k <;> simp_all [A, w] <;> norm_num

/-- Tightness of Theorem 20.5 for `m = 2`: the equilibrium `A` has makespan at least
`(2 - 2/3) · makespan(B) = 4`, so the bound `makespan_le_of_isPureNash` is attained. -/
example : (2 - 2 / ((2 : ℕ) + 1 : ℝ)) * makespan w B ≤ makespan w A := by
  have hB : makespan w B ≤ 3 := sup'_le _ _ (fun j _ => (load_B j).le)
  have hA : 4 ≤ makespan w A := load_A_zero ▸ load_le_makespan w A 0
  have : (2 - 2 / ((2 : ℕ) + 1 : ℝ)) = 4 / 3 := by norm_num
  rw [this]
  linarith

/-- The theorem applied to the example. -/
example : makespan w A ≤ (2 - 2 / ((2 : ℕ) + 1 : ℝ)) * makespan w B :=
  makespan_le_of_isPureNash (fun i => by fin_cases i <;> norm_num [w]) isPureNash_A B

end MathlibExtTest.GameTheory.LoadBalancing
