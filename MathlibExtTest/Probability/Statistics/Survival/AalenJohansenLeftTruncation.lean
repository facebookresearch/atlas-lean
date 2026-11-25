/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.AalenJohansenLeftTruncation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

@[expose] public section

open Finset Matrix
open MathlibExt.Probability.Statistics.AalenJohansenProductIntegral
open MathlibExt.Probability.Statistics.LeftTruncation
open MathlibExt.Probability.Statistics.AalenJohansenLeftTruncation

namespace MathlibExtTest.Probability.Statistics.AalenJohansenLeftTruncation

/-- Two grid times `1 < 2`. -/
noncomputable def t : Fin 2 → ℝ := ![1, 2]

theorem t_strictMono : StrictMono t := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i; norm_num [t]

/-! ### Competing risks with one delayed entrant

Subject `0` is in from the start and fails from cause `0` at `t₀ = 1`; subject `1` is in from the
start and is censored at `t₁ = 2`; subject `2` enters exactly at `t₀` (entry index `0`, so it is
*not* at risk at `t₀`) and fails from cause `1` at `t₁`. -/

/-- The left-truncated survival data. -/
noncomputable def E : DelayedEntryData 2 3 where
  time := t
  strictMono_time := t_strictMono
  entry := ![⊥, ⊥, ((0 : Fin 2) : WithBot (Fin 2))]
  exit := ![0, 1, 1]
  event := ![true, false, true]
  entry_lt_exit := by decide

/-- The failure causes (the censored subject's label is irrelevant). -/
def cause : Fin 3 → Fin 2 := ![0, 0, 1]

/-- The competing-risks multi-state data. -/
noncomputable def D : DelayedEntryMultiStateData 2 3 (Option (Fin 2)) := ofCompetingRisks E cause

/-- The entry at `L = 1 = t₀` has entry index `0`: from the definition of `entryIndex`. -/
example : entryIndex t 1 = ((0 : Fin 2) : WithBot (Fin 2)) := by
  have h : ∀ j : Fin 2, (t j ≤ 1 ↔ j = 0) := Fin.forall_fin_two.2 ⟨by norm_num [t], by norm_num [t]⟩
  have hset : univ.filter (fun j : Fin 2 => t j ≤ 1) = {0} := by
    ext j; simp [h]
  rw [entryIndex, hset, max_singleton]

/-! #### Counts, from the definitions -/

/-- Delayed entry removes subject `2` from the risk set at `t₀`: `Y(t₀) = 2`, not `3`. -/
theorem D_atRisk :
    D.atRisk 0 none = 2 ∧ D.atRisk 1 none = 2 ∧ ∀ j c, D.atRisk j (some c) = 0 := by
  decide

theorem D_forgetEntry_atRisk :
    D.forgetEntry.atRisk 0 none = 3 ∧ D.forgetEntry.atRisk 1 none = 2 := by
  decide

theorem D_transitions :
    D.transitions 0 none (some 0) = 1 ∧ D.transitions 0 none (some 1) = 0 ∧
      D.transitions 1 none (some 0) = 0 ∧ D.transitions 1 none (some 1) = 1 ∧
      ∀ j c l, D.transitions j (some c) l = 0 := by
  decide

theorem D_forgetEntry_transitions :
    D.forgetEntry.transitions 0 none (some 0) = 1 ∧ D.forgetEntry.transitions 0 none (some 1) = 0 ∧
      D.forgetEntry.transitions 1 none (some 0) = 0 ∧
      D.forgetEntry.transitions 1 none (some 1) = 1 := by
  decide

/-- `∑_l N_{none, l}(t₀) = Y_none(t₀)`, by counting: one failure and one subject staying. -/
example : D.transitions 0 none none = 1 := by decide

/-! #### The estimator, from the definitions

The Nelson–Aalen jumps are `ΔΛ(t₀) = [[-1/2, 1/2, 0], 0, 0]` and `ΔΛ(t₁) = [[-1/2, 0, 1/2], 0, 0]`
(rows and columns ordered `none, some 0, some 1`), so the first row of
`(I + ΔΛ(t₀)) (I + ΔΛ(t₁))` is `(1/4, 1/2, 1/4)`. Without truncation `Y(t₀) = 3` and the first row
is `(1/3, 1/3, 1/3)`. -/

/-- The time-ordered product over two grid times, both in `(0, 2]`. -/
theorem orderedProd_two (A : Fin 2 → Matrix (Option (Fin 2)) (Option (Fin 2)) ℝ) :
    orderedProd A (fun j => 0 < t j ∧ t j ≤ 2) = (1 + A 0) * (1 + A 1) := by
  have h0 : 0 < t 0 ∧ t 0 ≤ 2 := by norm_num [t]
  have h1 : 0 < t 1 ∧ t 1 ≤ 2 := by norm_num [t]
  simp only [orderedProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, Fin.succ_zero_eq_one]
  rw [ite_eq_left h0, ite_eq_left h1]

/-- The first row of `(1 + A) (1 + B)` when the rows `some c` of `B` vanish. -/
theorem prod_row_none (A B : Matrix (Option (Fin 2)) (Option (Fin 2)) ℝ)
    (hB : ∀ c l, B (some c) l = 0) (l : Option (Fin 2)) :
    ((1 + A) * (1 + B)) none l =
      (1 + A none none) * (1 + B) none l +
        (A none (some 0) * (1 : Matrix (Option (Fin 2)) (Option (Fin 2)) ℝ) (some 0) l +
          A none (some 1) * (1 : Matrix (Option (Fin 2)) (Option (Fin 2)) ℝ) (some 1) l) := by
  simp only [Matrix.mul_apply, Fintype.sum_option, Fin.sum_univ_two, Matrix.add_apply, hB, add_zero,
    one_apply_eq, one_apply_ne (Option.some_ne_none _).symm, zero_add]

/-- The Nelson–Aalen jumps of `D`, entry by entry. -/
theorem D_naIncrement :
    D.toMultiState.naIncrement 0 none none = -1 / 2 ∧
      D.toMultiState.naIncrement 0 none (some 0) = 1 / 2 ∧
      D.toMultiState.naIncrement 0 none (some 1) = 0 ∧
      D.toMultiState.naIncrement 1 none none = -1 / 2 ∧
      D.toMultiState.naIncrement 1 none (some 0) = 0 ∧
      D.toMultiState.naIncrement 1 none (some 1) = 1 / 2 ∧
      ∀ j c l, D.toMultiState.naIncrement j (some c) l = 0 := by
  obtain ⟨a0, a1, as⟩ := D_atRisk
  obtain ⟨n00, n01, n10, n11, ns⟩ := D_transitions
  simp only [MultiStateData.naIncrement, DelayedEntryMultiStateData.toMultiState,
    sum_erase_eq_sub (mem_univ _), Fintype.sum_option, Fin.sum_univ_two, a0, a1, as, n00, n01,
    n10, n11, ns, reduceCtorEq, ite_false, ite_true]
  norm_num

theorem D_forgetEntry_naIncrement :
    D.forgetEntry.toMultiState.naIncrement 0 none none = -1 / 3 ∧
      D.forgetEntry.toMultiState.naIncrement 0 none (some 0) = 1 / 3 ∧
      D.forgetEntry.toMultiState.naIncrement 0 none (some 1) = 0 ∧
      D.forgetEntry.toMultiState.naIncrement 1 none none = -1 / 2 ∧
      D.forgetEntry.toMultiState.naIncrement 1 none (some 0) = 0 ∧
      D.forgetEntry.toMultiState.naIncrement 1 none (some 1) = 1 / 2 := by
  obtain ⟨a0, a1⟩ := D_forgetEntry_atRisk
  obtain ⟨n00, n01, n10, n11⟩ := D_forgetEntry_transitions
  simp only [MultiStateData.naIncrement, DelayedEntryMultiStateData.toMultiState,
    sum_erase_eq_sub (mem_univ _), Fintype.sum_option, Fin.sum_univ_two, a0, a1, n00, n01,
    n10, n11, reduceCtorEq, ite_false, ite_true]
  norm_num

theorem D_forgetEntry_naIncrement_some (j : Fin 2) (c : Fin 2) (l : Option (Fin 2)) :
    D.forgetEntry.toMultiState.naIncrement j (some c) l = 0 := by
  have : D.forgetEntry.atRisk j (some c) = 0 := by revert j c; decide
  simp [MultiStateData.naIncrement, DelayedEntryMultiStateData.toMultiState, this]

/-- **The left-truncated Aalen–Johansen matrix, first row, from the definitions**:
`P̂(0, 2)` has first row `(1/4, 1/2, 1/4)`. -/
theorem D_transitionMatrix :
    D.transitionMatrix 0 2 none none = 1 / 4 ∧ D.transitionMatrix 0 2 none (some 0) = 1 / 2 ∧
      D.transitionMatrix 0 2 none (some 1) = 1 / 4 := by
  obtain ⟨a0nn, a0n0, a0n1, a1nn, a1n0, a1n1, as⟩ := D_naIncrement
  have hP : D.transitionMatrix 0 2 = (1 + D.toMultiState.naIncrement 0) *
      (1 + D.toMultiState.naIncrement 1) := orderedProd_two _
  rw [hP, prod_row_none _ _ (as 1), prod_row_none _ _ (as 1), prod_row_none _ _ (as 1)]
  simp only [Matrix.add_apply, one_apply_eq, one_apply_ne (Option.some_ne_none _).symm,
    one_apply_ne (Option.some_ne_none _), a0nn, a0n0, a0n1, a1nn, a1n0, a1n1]
  norm_num

/-- **Without truncation the estimate differs**: the untruncated matrix has first row
`(1/3, 1/3, 1/3)`. So the hypothesis of `transitionMatrix_eq_forgetEntry` (here violated by
subject `2`, who enters at `t₀`) cannot be dropped. -/
theorem D_forgetEntry_transitionMatrix :
    D.forgetEntry.transitionMatrix 0 2 none none = 1 / 3 ∧
      D.forgetEntry.transitionMatrix 0 2 none (some 0) = 1 / 3 ∧
      D.forgetEntry.transitionMatrix 0 2 none (some 1) = 1 / 3 := by
  obtain ⟨a0nn, a0n0, a0n1, a1nn, a1n0, a1n1⟩ := D_forgetEntry_naIncrement
  have hP : D.forgetEntry.transitionMatrix 0 2 = (1 + D.forgetEntry.toMultiState.naIncrement 0) *
      (1 + D.forgetEntry.toMultiState.naIncrement 1) := orderedProd_two _
  have as := D_forgetEntry_naIncrement_some 1
  rw [hP, prod_row_none _ _ as, prod_row_none _ _ as, prod_row_none _ _ as]
  simp only [Matrix.add_apply, one_apply_eq, one_apply_ne (Option.some_ne_none _).symm,
    one_apply_ne (Option.some_ne_none _), a0nn, a0n0, a0n1, a1nn, a1n0, a1n1]
  norm_num

example : D.transitionMatrix 0 2 ≠ D.forgetEntry.transitionMatrix 0 2 := fun h => by
  have := congr_fun (congr_fun h none) none
  rw [D_transitionMatrix.1, D_forgetEntry_transitionMatrix.1] at this
  norm_num at this

/-! #### Agreement with the closed forms, both sides from the definitions -/

/-- The delayed-entry product-limit factors of `LeftTruncation`: `Y = 2, 2` and `d = 1, 1`. -/
theorem E_plFactor : E.plFactor 0 = 1 / 2 ∧ E.plFactor 1 = 1 / 2 := by
  have hY : E.atRisk 0 = 2 ∧ E.atRisk 1 = 2 := by decide
  have hd : E.deaths 0 = 1 ∧ E.deaths 1 = 1 := by decide
  simp only [DelayedEntryData.plFactor, DelayedEntryData.hazardEst, hY.1, hY.2, hd.1, hd.2]
  norm_num

/-- `Ŝ(0, 2) = (1 - 1/2)(1 - 1/2) = 1/4`, the value of the matrix entry computed above. -/
example : condSurvival E 0 2 = D.transitionMatrix 0 2 none none := by
  have hset : univ.filter (fun j : Fin 2 => 0 < E.time j ∧ E.time j ≤ 2) = univ :=
    filter_true_of_mem fun j _ => by fin_cases j <;> norm_num [E, t]
  rw [condSurvival, hset, Fin.prod_univ_two, E_plFactor.1, E_plFactor.2, D_transitionMatrix.1]
  norm_num

/-- The theorem under test agrees with the direct computation. -/
example : condSurvival E 0 2 = 1 / 4 := by
  rw [← D_transitionMatrix.1]
  exact (transitionMatrix_none_none E cause 0 2).symm

example : condCumInc E cause 1 0 2 = 1 / 4 := by
  rw [← D_transitionMatrix.2.2]
  exact (transitionMatrix_none_some E cause 0 2 1).symm

/-- From before the first grid time, the delayed-entry product-limit `plSurvival` is `1/4`. -/
example : E.plSurvival 2 = 1 / 4 := by
  rw [← transitionMatrix_none_none_eq_plSurvival E cause (s := 0) (fun j => by
    fin_cases j <;> norm_num [E, t]), ← D_transitionMatrix.1]
  rfl

/-! #### Empty risk sets freeze absorbing states -/

/-- Nobody is at risk in an absorbing state, so its row of the estimator is the identity row. -/
example (c : Fin 2) (l : Option (Fin 2)) :
    D.transitionMatrix 0 2 (some c) l = (1 : Matrix _ _ ℝ) (some c) l :=
  D.transitionMatrix_apply_of_atRisk_eq_zero (fun j _ _ => D_atRisk.2.2 j c) l

/-! ### A reversible illness–death path with delayed entry

States `0` (healthy) and `1` (ill), recovery allowed. Subject `0` is in from the start, falls ill
at `t₀` and recovers at `t₁`; subject `1` enters exactly at `t₀`, healthy, and stays healthy
through `t₁`. -/

noncomputable def R : DelayedEntryMultiStateData 2 2 (Fin 2) where
  time := t
  strictMono_time := t_strictMono
  entry := ![⊥, ((0 : Fin 2) : WithBot (Fin 2))]
  exit := ![1, 1]
  state := ![![0, 1, 0], ![0, 0, 0]]
  entry_lt_exit := by decide

/-- At `t₀` only subject `0` is at risk (healthy); at `t₁` subject `0` is ill and subject `1`
healthy. -/
theorem R_counts :
    R.atRisk 0 0 = 1 ∧ R.atRisk 0 1 = 0 ∧ R.atRisk 1 0 = 1 ∧ R.atRisk 1 1 = 1 ∧
      R.transitions 0 0 1 = 1 ∧ R.transitions 1 1 0 = 1 ∧ R.transitions 1 0 0 = 1 := by
  decide

/-- Untruncated, subject `1` would be at risk (healthy) at `t₀` too. -/
example : R.forgetEntry.atRisk 0 0 = 2 := by decide

/-- The state-blind risk sets are those of `LeftTruncation`: `1` at `t₀`, `2` at `t₁`. -/
example : (R.toDelayedEntryData ![false, false]).atRisk 0 = 1 ∧
    (R.toDelayedEntryData ![false, false]).atRisk 1 = 2 := by
  decide

/-! ### The empty sample -/

/-- With no subjects every Nelson–Aalen jump is `0` and the estimator is the identity. -/
noncomputable def D₀ : DelayedEntryMultiStateData 2 0 (Fin 2) where
  time := t
  strictMono_time := t_strictMono
  entry := Fin.elim0
  exit := Fin.elim0
  state := Fin.elim0
  entry_lt_exit i := i.elim0

example (s u : ℝ) : D₀.transitionMatrix s u = 1 := by
  have hA : ∀ j, D₀.toMultiState.naIncrement j = 0 := fun j => by
    ext h l
    simp [MultiStateData.naIncrement, DelayedEntryMultiStateData.toMultiState,
      DelayedEntryMultiStateData.atRisk]
  have : (fun j => if s < D₀.time j ∧ D₀.time j ≤ u then 1 + D₀.toMultiState.naIncrement j
      else 1 : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) = fun _ => 1 :=
    funext fun j => by simp [hA]
  change orderedProd _ _ = 1
  rw [orderedProd]
  change (List.ofFn (fun j => if s < D₀.time j ∧ D₀.time j ≤ u then
    1 + D₀.toMultiState.naIncrement j else 1)).prod = 1
  rw [this, List.ofFn_const, List.prod_replicate, one_pow]

end MathlibExtTest.Probability.Statistics.AalenJohansenLeftTruncation
