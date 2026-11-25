/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.MechanismDesign.TruthfulScheduling
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.NormNum

/-!
# Tests for truthful scheduling on unrelated machines

Tests for `MathlibExt.GameTheory.MechanismDesign.TruthfulScheduling` on a
concrete 2-machine 2-task profile: `t1_loads_split` checks loads and makespan
under the split allocation, `t2_minwork_values` checks the MinWork makespan and
second-price payment, and `t3_opt_le_one` bounds the optimal makespan.
-/

set_option autoImplicit false

namespace MathlibExtTest.GameTheory.MechanismDesign.TruthfulScheduling

open MathlibExt.GameTheory.MechanismDesign.TruthfulScheduling

@[expose] public section

/-- The concrete 2-machine 2-task profile: machine 0 is fast (time 1) on
task 0 and slow (time 3) on task 1, machine 1 is the mirror image. -/
def tt : Fin 2 → Fin 2 → ℝ := fun i j =>
  if i = 0 then (if j = 0 then 1 else 3) else (if j = 0 then 3 else 1)

/-- The split allocation: each task goes to its same-indexed machine. -/
def splitA : Fin 2 → Fin 2 := fun j => j

/-- Under the split allocation both machine loads and the makespan equal 1. -/
theorem t1_loads_split :
    load tt splitA 0 = 1 ∧ load tt splitA 1 = 1 ∧ makespanOf tt splitA = 1 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have e0 : Finset.univ.filter (fun j : Fin 2 => splitA j = 0) = {0} := by
    decide
  have e1 : Finset.univ.filter (fun j : Fin 2 => splitA j = 1) = {1} := by
    decide
  have hload0 : load tt splitA 0 = 1 := by
    unfold load
    rw [e0, Finset.sum_singleton]
    simp [tt]
  have hload1 : load tt splitA 1 = 1 := by
    unfold load
    rw [e1, Finset.sum_singleton]
    simp [tt, h10]
  have hspan : makespanOf tt splitA = 1 := by
    unfold makespanOf
    apply le_antisymm
    · apply Finset.max'_le _ _ _ _
      intro y hy
      rw [Finset.mem_image] at hy
      rcases hy with ⟨i, _, rfl⟩
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl
      · rw [hload0]
      · rw [hload1]
    · apply Finset.le_max' _ _ _
      have h := Finset.mem_image_of_mem (load tt splitA) (Finset.mem_univ 0)
      rwa [hload0] at h
  exact ⟨hload0, hload1, hspan⟩

/-- MinWork achieves makespan 1 on `tt`, and machine 0 is paid 3 for its
winning task (the second-fastest time for task 0). -/
theorem t2_minwork_values :
    makespanOf tt (minWork tt) = 1 ∧ minWorkPayment tt 0 = 3 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have htt10 : tt 1 0 = 3 := by simp [tt, h10]
  have h0 : fastest tt 0 = 0 := by
    have h := fastest_spec tt 0 0
    simp [tt] at h
    by_cases hc : fastest tt 0 = 0
    · exact hc
    · simp [hc] at h
  have h1 : fastest tt 1 = 1 := by
    have h := fastest_spec tt 1 1
    simp [tt] at h
    by_cases hc : fastest tt 1 = 0
    · simp [hc] at h
    · have hm : fastest tt 1 = 1 := by omega
      exact hm
  have hmw : minWork tt = splitA := by
    funext j
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    · show fastest tt 0 = splitA 0
      rw [h0]
      rfl
    · show fastest tt 1 = splitA 1
      rw [h1]
      rfl
  have hspan : makespanOf tt (minWork tt) = 1 := by
    rw [hmw]
    exact t1_loads_split.2.2
  have hpay : minWorkPayment tt 0 = 3 := by
    unfold minWorkPayment
    rw [hmw]
    have hf : Finset.univ.filter (fun j : Fin 2 => splitA j = 0) = {0} := by
      decide
    rw [hf, Finset.sum_singleton]
    apply le_antisymm
    · apply Finset.min'_le _ _ _
      simp [htt10]
    · apply Finset.le_min' _ _ _ _
      intro y hy
      rw [Finset.mem_image] at hy
      rcases hy with ⟨k, hkmem, rfl⟩
      show (3 : ℝ) ≤ tt k 0
      rw [Finset.mem_erase] at hkmem
      have hk1 : k = 1 := by omega
      rw [hk1, htt10]
  exact ⟨hspan, hpay⟩

/-- The optimal makespan on `tt` is at most 1, witnessed by the split. -/
theorem t3_opt_le_one : optMakespan tt ≤ 1 := by
  have h := optMakespan_le tt splitA
  rw [t1_loads_split.2.2] at h
  exact h

end

end MathlibExtTest.GameTheory.MechanismDesign.TruthfulScheduling
