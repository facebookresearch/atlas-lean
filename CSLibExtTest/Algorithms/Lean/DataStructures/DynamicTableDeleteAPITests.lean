/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.DynamicTable.Delete

/-! Ordinary downstream consumers of the dynamic-table deletion and lookup API,
with arbitrary payloads and no equality instances. -/

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.DynamicTable.DeleteAPITests

variable {α : Type u} (T : Table α)

#check @Table
#check @WellFormed
#check @DynamicTable.get?
#check @tableDelete
#check @get?_eq_none_of_le
#check @get?_isSome_iff
#check @tableDelete_num
#check @tableDelete_size
#check @tableDelete_slots
#check @tableDelete_wellFormed
#check @tableDelete_contents
#check @get?_delete_of_lt
#check @get?_delete_last

example : (tableDelete T).num = T.num - 1 := tableDelete_num T

example : (tableDelete T).slots.size =
    if T.num = 0 then T.slots.size
    else if 4 * (T.num - 1) < T.slots.size then T.slots.size / 2
    else T.slots.size :=
  tableDelete_size T

-- Empty deletion leaves capacity unchanged and lookup empty.
example (h : T.num = 0) : (tableDelete T).slots.size = T.slots.size := by
  rw [tableDelete_size]
  simp [h]

example : get? (empty : Table α) 0 = none := by
  have h : (empty : Table α).num = 0 := by rw [empty_eq]
  exact get?_eq_none_of_le _ (by omega)

example : get? (tableDelete (empty : Table α)) 0 = none := by
  have h : (empty : Table α).num = 0 := by rw [empty_eq]
  have hlast := get?_delete_last (empty : Table α)
  rwa [h] at hlast

-- Exact quarter after deletion (`2` of `8`) does not contract; below
-- quarter (`1` of `8`) halves the capacity.
example (hnum : T.num = 3) (hsize : T.slots.size = 8) :
    (tableDelete T).slots.size = 8 := by
  rw [tableDelete_size]
  simp [hnum, hsize]

example (hnum : T.num = 2) (hsize : T.slots.size = 8) :
    (tableDelete T).slots.size = 4 := by
  rw [tableDelete_size]
  simp [hnum, hsize]

-- Deleting the sole item of a one-slot table contracts to capacity zero.
example (hnum : T.num = 1) (hsize : T.slots.size = 1) :
    (tableDelete T).slots.size = 0 := by
  rw [tableDelete_size]
  simp [hnum, hsize]

example (h : WellFormed T) (hnum : T.num ≠ 0) : (tableDelete T).slots =
    T.slots.extract 0 (T.num - 1) ++
      Array.replicate ((tableDelete T).slots.size - (T.num - 1)) none :=
  tableDelete_slots T h hnum

example (h : WellFormed T) : WellFormed (tableDelete T) :=
  tableDelete_wellFormed T h

example (h : WellFormed T) :
    (contents (tableDelete T)).toList = (contents T).toList.dropLast :=
  tableDelete_contents T h

example {i : Nat} (h : T.num ≤ i) : get? T i = none :=
  get?_eq_none_of_le T h

example (h : WellFormed T) (i : Nat) : (get? T i).isSome ↔ i < T.num :=
  get?_isSome_iff T h i

example (h : WellFormed T) {i : Nat} (hi : i < T.num - 1) :
    get? (tableDelete T) i = get? T i :=
  get?_delete_of_lt T h hi

example : get? (tableDelete T) (T.num - 1) = none :=
  get?_delete_last T

#print axioms tableDelete_num
#print axioms tableDelete_size
#print axioms tableDelete_slots
#print axioms tableDelete_wellFormed
#print axioms tableDelete_contents
#print axioms get?_isSome_iff
#print axioms get?_delete_of_lt
#print axioms get?_delete_last

end Cslib.Algorithms.Lean.DynamicTable.DeleteAPITests
