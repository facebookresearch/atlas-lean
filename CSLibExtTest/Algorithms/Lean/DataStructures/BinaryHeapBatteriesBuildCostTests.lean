/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.BatteriesBuildCost
import all Batteries.Data.BinaryHeap.Basic
import all Batteries.Data.BinaryHeap.Lemmas

/-! # Stored consumers of counted Batteries bottom-up construction

The concrete runs below use the actual selector, sift-down branch equations, and
build-loop equations. They are not runtime witnesses. The arithmetic negative is
about depth differences, not actual subtree heights.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BatteriesBuildCostTests

private theorem empty_run :
    TimeM.mkHeap (⟨#[], rfl⟩ : Vector Nat 0) = ⟨⟨#[], rfl⟩, (0, 0)⟩ := by
  rfl

private theorem singleton_run (x : Nat) :
    TimeM.mkHeap (⟨#[x], rfl⟩ : Vector Nat 1) = ⟨⟨#[x], rfl⟩, (0, 0)⟩ := by
  rfl

private theorem empty_erasure :
    (TimeM.mkHeap (⟨#[], rfl⟩ : Vector Nat 0)).ret =
      Batteries.BinaryHeap.mkHeap ⟨#[], rfl⟩ :=
  TimeM.ret_mkHeap _

private theorem singleton_erasure (x : Nat) :
    (TimeM.mkHeap (⟨#[x], rfl⟩ : Vector Nat 1)).ret =
      Batteries.BinaryHeap.mkHeap ⟨#[x], rfl⟩ :=
  TimeM.ret_mkHeap _

private def ascendingSeven : Vector Nat 7 := ⟨#[1, 2, 3, 4, 5, 6, 7], rfl⟩
private def afterTwo : Vector Nat 7 := ⟨#[1, 2, 7, 4, 5, 6, 3], rfl⟩
private def afterOne : Vector Nat 7 := ⟨#[1, 5, 7, 4, 2, 6, 3], rfl⟩
private def afterRootSwap : Vector Nat 7 := ⟨#[7, 5, 1, 4, 2, 6, 3], rfl⟩
private def builtSeven : Vector Nat 7 := ⟨#[7, 5, 6, 4, 2, 1, 3], rfl⟩

private theorem ascending_down_two :
    TimeM.heapifyDown ascendingSeven ⟨2, by decide⟩ = ⟨afterTwo, (2, 1)⟩ := by
  have hleaf := TimeM.heapifyDown_eq_of_maxChild_none afterTwo ⟨6, by decide⟩ (by decide)
  have hswap : ascendingSeven.swap (⟨2, by decide⟩ : Fin 7)
      (⟨6, by decide⟩ : Fin 7) = afterTwo := by rfl
  rw [TimeM.heapifyDown_eq_of_lt_child ascendingSeven
    ⟨2, by decide⟩ ⟨6, by decide⟩ (by decide) (by decide), hswap]
  simp only [hleaf]
  rfl

private theorem ascending_down_one :
    TimeM.heapifyDown afterTwo ⟨1, by decide⟩ = ⟨afterOne, (2, 1)⟩ := by
  have hleaf := TimeM.heapifyDown_eq_of_maxChild_none afterOne ⟨4, by decide⟩ (by decide)
  have hswap : afterTwo.swap (⟨1, by decide⟩ : Fin 7)
      (⟨4, by decide⟩ : Fin 7) = afterOne := by rfl
  rw [TimeM.heapifyDown_eq_of_lt_child afterTwo
    ⟨1, by decide⟩ ⟨4, by decide⟩ (by decide) (by decide), hswap]
  simp only [hleaf]
  rfl

private theorem ascending_root_child :
    TimeM.heapifyDown afterRootSwap ⟨2, by decide⟩ = ⟨builtSeven, (2, 1)⟩ := by
  have hleaf := TimeM.heapifyDown_eq_of_maxChild_none builtSeven ⟨5, by decide⟩ (by decide)
  have hswap : afterRootSwap.swap (⟨2, by decide⟩ : Fin 7)
      (⟨5, by decide⟩ : Fin 7) = builtSeven := by rfl
  rw [TimeM.heapifyDown_eq_of_lt_child afterRootSwap
    ⟨2, by decide⟩ ⟨5, by decide⟩ (by decide) (by decide), hswap]
  simp only [hleaf]
  rfl

private theorem ascending_down_zero :
    TimeM.heapifyDown afterOne ⟨0, by decide⟩ = ⟨builtSeven, (4, 2)⟩ := by
  have hswap : afterOne.swap (⟨0, by decide⟩ : Fin 7)
      (⟨2, by decide⟩ : Fin 7) = afterRootSwap := by rfl
  rw [TimeM.heapifyDown_eq_of_lt_child afterOne
    ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide), hswap]
  simp only [ascending_root_child]
  rfl

private theorem ascending_seven_run :
    TimeM.mkHeap ascendingSeven = ⟨builtSeven, (8, 4)⟩ := by
  apply TimeM.ext <;>
    simp only [TimeM.mkHeap, TimeM.mkHeap.loop, TimeM.ret_bind, TimeM.time_bind,
      ascending_down_two, ascending_down_one, ascending_down_zero,
      TimeM.ret_pure, TimeM.time_pure]
  rfl

private theorem ascending_seven_canonical_result :
    Batteries.BinaryHeap.mkHeap ascendingSeven = builtSeven := by
  rw [← TimeM.ret_mkHeap, ascending_seven_run]

private theorem ascending_seven_exact_counts :
    (TimeM.mkHeap ascendingSeven).time = (8, 4) := by
  rw [ascending_seven_run]

private theorem ascending_seven_linear_bound :
    (TimeM.mkHeap ascendingSeven).time.1 + (TimeM.mkHeap ascendingSeven).time.2 ≤ 6 * 7 :=
  TimeM.mkHeap_time_le ascendingSeven

private def descendingSeven : Vector Nat 7 := ⟨#[7, 6, 5, 4, 3, 2, 1], rfl⟩

private theorem descending_seven_run :
    TimeM.mkHeap descendingSeven = ⟨descendingSeven, (6, 0)⟩ := by
  have htwo := TimeM.heapifyDown_eq_of_not_lt_child descendingSeven
    ⟨2, by decide⟩ ⟨5, by decide⟩ (by decide) (by decide)
  have hone := TimeM.heapifyDown_eq_of_not_lt_child descendingSeven
    ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide)
  have hzero := TimeM.heapifyDown_eq_of_not_lt_child descendingSeven
    ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) (by decide)
  apply TimeM.ext <;>
    simp only [TimeM.mkHeap, TimeM.mkHeap.loop, TimeM.ret_bind, TimeM.time_bind,
      htwo, hone, hzero, TimeM.ret_pure, TimeM.time_pure]
  rfl

private theorem descending_seven_erasure :
    (TimeM.mkHeap descendingSeven).ret = Batteries.BinaryHeap.mkHeap descendingSeven :=
  TimeM.ret_mkHeap _

private def duplicateSeven : Vector Nat 7 := ⟨#[4, 4, 4, 4, 4, 4, 4], rfl⟩

private theorem duplicate_selects_left :
    (TimeM.timedMaxChild duplicateSeven ⟨0, by decide⟩).ret = some ⟨1, by decide⟩ := by
  rfl

private theorem duplicate_selection_cost :
    (TimeM.timedMaxChild duplicateSeven ⟨0, by decide⟩).time = (1, 0) := by
  rfl

private theorem duplicate_seven_run :
    TimeM.mkHeap duplicateSeven = ⟨duplicateSeven, (6, 0)⟩ := by
  have htwo := TimeM.heapifyDown_eq_of_not_lt_child duplicateSeven
    ⟨2, by decide⟩ ⟨5, by decide⟩ (by decide) (by decide)
  have hone := TimeM.heapifyDown_eq_of_not_lt_child duplicateSeven
    ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide)
  have hzero := TimeM.heapifyDown_eq_of_not_lt_child duplicateSeven
    ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) (by decide)
  apply TimeM.ext <;>
    simp only [TimeM.mkHeap, TimeM.mkHeap.loop, TimeM.ret_bind, TimeM.time_bind,
      htwo, hone, hzero, TimeM.ret_pure, TimeM.time_pure]
  rfl

private theorem duplicate_seven_erasure :
    (TimeM.mkHeap duplicateSeven).ret = Batteries.BinaryHeap.mkHeap duplicateSeven :=
  TimeM.ret_mkHeap _

private theorem one_child_selection_is_free :
    (TimeM.timedMaxChild (⟨#[1, 2], rfl⟩ : Vector Nat 2) ⟨0, by decide⟩).time = (0, 0) := by
  rfl

private theorem one_child_run :
    TimeM.mkHeap (⟨#[1, 2], rfl⟩ : Vector Nat 2) = ⟨⟨#[2, 1], rfl⟩, (1, 1)⟩ := by
  have hleaf := TimeM.heapifyDown_eq_of_maxChild_none
    (⟨#[2, 1], rfl⟩ : Vector Nat 2) ⟨1, by decide⟩ (by decide)
  have hroot : TimeM.heapifyDown (⟨#[1, 2], rfl⟩ : Vector Nat 2) ⟨0, by decide⟩ =
      ⟨⟨#[2, 1], rfl⟩, (1, 1)⟩ := by
    have hswap : (⟨#[1, 2], rfl⟩ : Vector Nat 2).swap (⟨0, by decide⟩ : Fin 2)
        (⟨1, by decide⟩ : Fin 2) = ⟨#[2, 1], rfl⟩ := by rfl
    rw [TimeM.heapifyDown_eq_of_lt_child (⟨#[1, 2], rfl⟩ : Vector Nat 2)
      ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) (by decide), hswap]
    simp only [hleaf]
    rfl
  apply TimeM.ext <;>
    simp only [TimeM.mkHeap, TimeM.mkHeap.loop, TimeM.ret_bind, TimeM.time_bind,
      hroot, TimeM.ret_pure, TimeM.time_pure]
  rfl

private theorem generic_erasure {α : Type} [Ord α] {size : Nat}
    (a : Vector α size) :
    (TimeM.mkHeap a).ret = Batteries.BinaryHeap.mkHeap a :=
  TimeM.ret_mkHeap a

private theorem generic_permutation {α : Type} [Ord α] {size : Nat}
    (a : Vector α size) : (TimeM.mkHeap a).ret.toArray.Perm a.toArray := by
  rw [TimeM.ret_mkHeap]
  exact Batteries.BinaryHeap.mkHeap_perm

private theorem generic_well_formed {α : Type} [Ord α] [Std.TransOrd α] {size : Nat}
    (a : Vector α size) : Batteries.BinaryHeap.WF.TopDown (TimeM.mkHeap a).ret := by
  rw [TimeM.ret_mkHeap]
  exact Batteries.BinaryHeap.mkHeap_wf

private theorem generic_loop_well_formed {α : Type} [Ord α] [Std.TransOrd α]
    {size n : Nat} (a : Vector α size) (h : n ≤ size)
    (hinv : ∀ k : Fin size, n ≤ k.val → Batteries.BinaryHeap.WF.Children a k) :
    Batteries.BinaryHeap.WF.TopDown (TimeM.mkHeap.loop n a h).ret := by
  rw [TimeM.ret_mkHeap_loop]
  exact Batteries.BinaryHeap.mkHeap.loop_wf hinv

private theorem generic_sift_permutation {α : Type} [Ord α] {size : Nat}
    (a : Vector α size) (i : Fin size) : (TimeM.heapifyDown a i).ret.Perm a := by
  rw [TimeM.ret_heapifyDown]
  exact Batteries.BinaryHeap.heapifyDown_perm

private theorem generic_sift_well_formed {α : Type} [Ord α] [Std.TransOrd α]
    {size : Nat} (a : Vector α size) (i : Fin size)
    (hbelow : Batteries.BinaryHeap.WF.Below a i) :
    Batteries.BinaryHeap.WF.Children (TimeM.heapifyDown a i).ret i ∧
      Batteries.BinaryHeap.WF.Below (TimeM.heapifyDown a i).ret i := by
  rw [TimeM.ret_heapifyDown]
  exact Batteries.BinaryHeap.heapifyDown_wf hbelow

private theorem generic_sift_depth_bound {α : Type} [Ord α] {size : Nat}
    (a : Vector α size) (i : Fin size) :
    (TimeM.heapifyDown a i).time.1 + (TimeM.heapifyDown a i).time.2 ≤
      3 * (Nat.log2 size - Nat.log2 (i.val + 1)) :=
  TimeM.heapifyDown_time_le a i

private theorem generic_build_linear_bound {α : Type} [Ord α] {size : Nat}
    (a : Vector α size) : (TimeM.mkHeap a).time.1 + (TimeM.mkHeap a).time.2 ≤ 6 * size :=
  TimeM.mkHeap_time_le a

private theorem depth_difference_sum_at_sixteen :
    (∑ i ∈ Finset.range (16 / 2), (Nat.log2 16 - Nat.log2 (i + 1))) = 19 := by
  decide

private theorem coefficient_one_fails_for_depth_difference_sum :
    ¬(∑ i ∈ Finset.range (16 / 2), (Nat.log2 16 - Nat.log2 (i + 1))) ≤ 16 := by
  rw [depth_difference_sum_at_sixteen]
  decide

end Cslib.Algorithms.Lean.BatteriesBuildCostTests
