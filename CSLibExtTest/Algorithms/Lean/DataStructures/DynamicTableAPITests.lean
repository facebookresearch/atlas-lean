/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.DynamicTable.Basic

/-! Ordinary downstream consumers, with arbitrary payloads and no equality instances. -/

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.DynamicTable.APITests

variable {α : Type u} (T : Table α) (x : α) (xs : Array α)

#check @Table
#check @WellFormed
#check @contents
#check @empty
#check @tableInsert
#check @tableInsertMany

example : (tableInsert T x).ret.num = T.num + 1 := tableInsert_num T x

example : (tableInsert T x).ret.slots.size =
    if T.slots.size = 0 then 1
    else if T.num = T.slots.size then 2 * T.slots.size else T.slots.size :=
  tableInsert_size T x

example (h : WellFormed T) : (tableInsert T x).ret.slots =
    T.slots.extract 0 T.num ++ #[some x] ++
      Array.replicate ((tableInsert T x).ret.slots.size - (T.num + 1)) none :=
  tableInsert_slots T x h

example (h : WellFormed T) : contents (tableInsert T x).ret = (contents T).push x :=
  tableInsert_contents T x h

example (h : WellFormed T) : WellFormed (tableInsert T x).ret :=
  tableInsert_wellFormed T x h

example : (tableInsert T x).time =
    1 + if T.slots.size > 0 ∧ T.num = T.slots.size then T.num else 0 :=
  tableInsert_time T x

example : ((tableInsert T x).time : Int) +
    (2 * ((tableInsert T x).ret.num : Int) - ((tableInsert T x).ret.slots.size : Int)) -
    (2 * (T.num : Int) - (T.slots.size : Int)) ≤ 3 := tableInsert_amortized T x

example (h : WellFormed T) : contents (tableInsertMany T xs).ret = contents T ++ xs :=
  tableInsertMany_contents T xs h

example (h : WellFormed T) : WellFormed (tableInsertMany T xs).ret :=
  tableInsertMany_wellFormed T xs h

example : (tableInsertMany empty xs).ret.slots.size ≤ 2 * xs.size :=
  tableInsertMany_size_le xs

example : (tableInsertMany empty xs).time ≤ 3 * xs.size := tableInsertMany_time_le xs

example (h : xs.size > 0) : (tableInsertMany empty xs).time < 3 * xs.size :=
  tableInsertMany_time_lt xs h

example (hT : WellFormed T) (i : Nat) (hi : i < T.slots.size) :
    T.slots[i].isSome ↔ i < T.num :=
  (wellFormed_iff T).mp hT i hi

example (hT : ∀ (i : Nat) (hi : i < T.slots.size), T.slots[i].isSome ↔ i < T.num) :
    WellFormed T :=
  (wellFormed_iff T).mpr hT

example : contents T = (T.slots.extract 0 T.num).filterMap id :=
  contents_eq T

example : (empty : Table α).num = 0 := by
  rw [empty_eq]

example : (empty : Table α).slots = #[] := by
  rw [empty_eq]

example : WellFormed (empty : Table α) := by
  apply (wellFormed_iff _).mpr
  rw [empty_eq]
  intro i hi
  simp only [Array.size_empty] at hi
  exact False.elim (Nat.not_lt_zero _ hi)

end Cslib.Algorithms.Lean.DynamicTable.APITests
