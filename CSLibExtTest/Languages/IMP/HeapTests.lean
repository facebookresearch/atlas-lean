/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.Heap

@[expose] public section

namespace Cslib.IMP.Tests

example : (Finmap.singleton 3 7 : Heap).lookup 3 = some 7 :=
  Finmap.lookup_singleton_eq

example : (Finmap.singleton 3 7 : Heap).lookup 4 = none := by
  rw [Finmap.lookup_eq_none, Finmap.mem_singleton]
  decide

example : (Finmap.insert 2 99 (Finmap.singleton 2 20) : Heap).lookup 2 = some 99 :=
  Finmap.lookup_insert _

example : (Finmap.insert 1 10 (Finmap.singleton 2 20) : Heap).lookup 2 = some 20 := by
  rw [Finmap.lookup_insert_of_ne _ (by decide : (2 : Nat) ≠ 1)]
  exact Finmap.lookup_singleton_eq

def twoCell : Heap := Finmap.insert 1 10 (Finmap.singleton 2 20)

example : twoCell.lookup 1 = some 10 := Finmap.lookup_insert _

example : twoCell.lookup 2 = some 20 := by simp [twoCell]

example : twoCell.lookup 3 = none := by simp [twoCell, Finmap.lookup_eq_none]

example : (1 : Nat) ∈ twoCell := by simp [twoCell]

example : (2 : Nat) ∈ twoCell := by simp [twoCell]

example : (3 : Nat) ∉ twoCell := by simp [twoCell]

example : (Finmap.erase 2 twoCell).lookup 2 = none := Finmap.lookup_erase _ _

example : (Finmap.erase 2 twoCell).lookup 1 = some 10 := by
  rw [Finmap.lookup_erase_ne (by decide : (1 : Nat) ≠ 2)]
  exact Finmap.lookup_insert _

example : Heap.Disjoint (Finmap.singleton 1 10) (Finmap.singleton 2 20) := by
  rw [Heap.disjoint_singleton_left]
  simp

example : (Finmap.singleton 1 10 ∪ Finmap.singleton 2 20 : Heap) =
    Finmap.singleton 2 20 ∪ Finmap.singleton 1 10 :=
  Finmap.union_comm_of_disjoint (Heap.disjoint_singleton_left.mpr (by simp))

def heap12 : Heap := Finmap.singleton 1 10 ∪ Finmap.singleton 2 20

example : heap12.lookup 1 = some 10 := by simp [heap12]

example : heap12.lookup 2 = some 20 := by simp [heap12]

example : heap12.lookup 3 = none := by simp [heap12, Finmap.lookup_eq_none]

example : Finmap.insert 1 10 (Finmap.erase 1 twoCell) = twoCell := by
  apply Heap.insert_erase_eq_self
  simp [twoCell]

example : Finmap.insert 3 30
      ((Finmap.singleton 1 10 ∪ Finmap.singleton 2 20 : Heap)) =
    Finmap.insert 3 30 (Finmap.singleton 1 10) ∪ Finmap.singleton 2 20 :=
  Finmap.insert_union

example : (Finmap.insert 3 30 (Finmap.singleton 1 10) ∪ Finmap.singleton 2 20 :
    Heap).lookup 3 = some 30 := by
  simp

example : Finmap.erase 1
      ((Finmap.singleton 1 10 ∪ Finmap.singleton 2 20 : Heap)) =
    Finmap.erase 1 (Finmap.singleton 1 10) ∪ Finmap.singleton 2 20 := by
  apply Heap.erase_union_of_notMem
  simp

example : ∃ a, a ∉ twoCell ∧ twoCell.lookup a = none := by
  obtain ⟨a, ha⟩ := Heap.exists_notMem twoCell
  exact ⟨a, ha, Finmap.lookup_eq_none.mpr ha⟩

end Cslib.IMP.Tests
