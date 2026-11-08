/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DynamicTable.Basic
import Batteries.Data.Array.Lemmas

/-!
# Dynamic-table deletion and lookup

Deletion follows CLRS, fourth edition, Section 16.4.2: removing the last item
contracts the table to half capacity when the load factor drops below `1/4`.

Design choice: `tableDelete` is a pure `Table α → Table α`, not a `TimeM`
executor like `tableInsert` in `Basic`, because the timed copying routine
`copyItems` is private to `Basic`; a copy-cost account of deletion is deferred.
Contraction is implemented by rebuilding the slot array as the occupied prefix
followed by empty slots; without contraction the last slot is cleared in
place. Deleting the sole item of a one-slot table contracts to capacity zero,
matching the initially unallocated `empty` table of `Basic`.

`Basic` has no lookup operation, so this module also adds `get?`, indexed by
logical position.
-/

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.DynamicTable

private lemma extract_size_of_le {β : Type u} (a : Array β) {k : Nat}
    (hk : k ≤ a.size) : (a.extract 0 k).size = k := by
  simp only [Array.size_extract, Nat.min_eq_left hk, Nat.sub_zero]

private lemma wellFormed_apply {α : Type u} {T : Table α} (hT : WellFormed T)
    (i : Nat) (h : i < T.slots.size) : (T.slots[i]'h).isSome ↔ i < T.num :=
  (wellFormed_iff T).mp hT i h

/-- Lookup by logical position; positions at or beyond `num` return `none`. -/
public def get? {α : Type u} (T : Table α) (i : Nat) : Option α :=
  if i < T.num then (T.slots[i]?).bind id else none

/-- Lookup outside the logical range always returns `none`. -/
public theorem get?_eq_none_of_le {α : Type u} (T : Table α) {i : Nat}
    (h : T.num ≤ i) : get? T i = none := by
  have hnot : ¬i < T.num := by omega
  simp [get?, hnot]

/-- In a well-formed table, lookup returns a value exactly on the logical range. -/
public theorem get?_isSome_iff {α : Type u} (T : Table α) (hT : WellFormed T)
    (i : Nat) : (get? T i).isSome ↔ i < T.num := by
  constructor
  · intro h
    by_contra hle
    rw [get?_eq_none_of_le T (Nat.le_of_not_gt hle)] at h
    exact Bool.noConfusion h
  · intro hi
    have hlt : i < T.slots.size := by have h := T.num_le; omega
    have hsome : (T.slots[i]'hlt).isSome = true := (wellFormed_apply hT i hlt).mpr hi
    simp [get?, hi, Array.getElem?_eq_getElem hlt, hsome]

/--
TABLE-DELETE for the last item. After decrementing `num`, contract to half
capacity when `4 * num < size`, that is, when the new load factor is
strictly below `1/4`; otherwise clear the vacated slot in place.
-/
public def tableDelete {α : Type u} (T : Table α) : Table α :=
  if hnum : T.num = 0 then T
  else if hcon : 4 * (T.num - 1) < T.slots.size then
    ⟨T.slots.extract 0 (T.num - 1) ++
        Array.replicate (T.slots.size / 2 - (T.num - 1)) none, T.num - 1, by
      have hkle : T.num - 1 ≤ T.slots.size := by have h := T.num_le; omega
      have he : (T.slots.extract 0 (T.num - 1)).size = T.num - 1 :=
        extract_size_of_le T.slots hkle
      simp only [Array.size_append, he, Array.size_replicate]
      omega⟩
  else
    ⟨T.slots.set (T.num - 1) none (by have h := T.num_le; omega), T.num - 1, by
      simp only [Array.size_set]
      have h := T.num_le
      omega⟩

/-- Deletion decrements the item count, with an empty table left at zero. -/
public theorem tableDelete_num {α : Type u} (T : Table α) :
    (tableDelete T).num = T.num - 1 := by
  by_cases h0 : T.num = 0
  · simp [tableDelete, h0]
  · by_cases hcon : 4 * (T.num - 1) < T.slots.size
    · simp [tableDelete, h0, hcon]
    · simp [tableDelete, h0, hcon]

/-- Deletion leaves capacity unchanged except for halving on contraction. -/
public theorem tableDelete_size {α : Type u} (T : Table α) :
    (tableDelete T).slots.size =
      if T.num = 0 then T.slots.size
      else if 4 * (T.num - 1) < T.slots.size then T.slots.size / 2
      else T.slots.size := by
  by_cases h0 : T.num = 0
  · simp [tableDelete, h0]
  · by_cases hcon : 4 * (T.num - 1) < T.slots.size
    · have he : (T.slots.extract 0 (T.num - 1)).size = T.num - 1 :=
        extract_size_of_le T.slots (by have h := T.num_le; omega)
      simp only [tableDelete, h0, hcon, ↓reduceDIte, ↓reduceIte, Array.size_append, he,
        Array.size_replicate]
      omega
    · simp only [tableDelete, h0, hcon, ↓reduceDIte, ↓reduceIte, Array.size_set]

private lemma extract_zero_extract_zero {β : Type u} (a : Array β) (k : Nat) :
    (a.extract 0 k).extract 0 k = a.extract 0 k := by
  apply Array.ext
  · simp only [Array.size_extract, Nat.sub_zero]
    omega
  · intro i _ _
    simp only [Array.getElem_extract, Nat.zero_add]

private lemma extract_append_prefix {β : Type u} (a b : Array β) {k : Nat}
    (hk : k ≤ a.size) : ((a.extract 0 k) ++ b).extract 0 k = a.extract 0 k := by
  rw [Array.extract_append_of_stop_le_size_left
      (by have h := extract_size_of_le a hk; omega),
    extract_zero_extract_zero]

private lemma extract_succ_push {β : Type u} (a : Array β) {k : Nat}
    (hk : k < a.size) : a.extract 0 (k + 1) = (a.extract 0 k).push a[k] := by
  apply Array.ext
  · simp only [Array.size_extract, Array.size_push, Nat.sub_zero]
    omega
  · intro i hi _
    have hi' : i < k + 1 := by
      have h := hi
      simp only [Array.size_extract, Nat.sub_zero] at h
      omega
    rw [Array.getElem_extract, Array.getElem_push]
    by_cases hik : i < (a.extract 0 k).size
    · rw [dite_eq_left hik, Array.getElem_extract]
    · have hsize : (a.extract 0 k).size = k :=
        extract_size_of_le a (by omega)
      have hik2 : i = k := by omega
      rw [dite_eq_right hik]
      subst hik2
      simp only [Nat.zero_add]

private lemma extract_num_push {α : Type u} (T : Table α) (hnum : T.num ≠ 0) :
    T.slots.extract 0 T.num =
      (T.slots.extract 0 (T.num - 1)).push
        (T.slots[T.num - 1]'(by have h := T.num_le; omega)) := by
  have hk : T.num - 1 < T.slots.size := by have h := T.num_le; omega
  have h := extract_succ_push T.slots hk
  rw [show T.num - 1 + 1 = T.num by omega] at h
  exact h

private lemma wellFormed_of_slots {α : Type u} (T out : Table α) (k n : Nat)
    (hT : WellFormed T) (hnum : out.num = k) (hk : k ≤ T.num)
    (hslots : out.slots = T.slots.extract 0 k ++ Array.replicate n none) :
    WellFormed out := by
  rcases out with ⟨slots, num, bound⟩
  dsimp only at hnum hslots
  obtain rfl : num = k := hnum
  subst slots
  have he : (T.slots.extract 0 num).size = num :=
    extract_size_of_le _ (by have h := T.num_le; omega)
  apply (wellFormed_iff _).mpr
  intro i hi
  change ((T.slots.extract 0 num ++ Array.replicate n none)[i]'hi).isSome ↔ i < num
  by_cases hn : i < num
  · have hl : i < (T.slots.extract 0 num).size := by omega
    rw [Array.getElem_append_left hl, Array.getElem_extract]
    simp only [Nat.zero_add]
    exact ⟨fun _ => hn,
      fun _ => (wellFormed_apply hT i (by have h := T.num_le; omega)).mpr (by omega)⟩
  · rw [Array.getElem_append_right (by omega), Array.getElem_replicate]
    exact ⟨fun h => Bool.noConfusion h, fun h => (hn h).elim⟩

/-- After deleting from a nonempty well-formed table, the slots are the
retained occupied prefix followed by empty slots. -/
public theorem tableDelete_slots {α : Type u} (T : Table α) (hT : WellFormed T)
    (hnum : T.num ≠ 0) :
    (tableDelete T).slots =
      T.slots.extract 0 (T.num - 1) ++
        Array.replicate ((tableDelete T).slots.size - (T.num - 1)) none := by
  have hle := T.num_le
  have hkle : T.num - 1 ≤ T.slots.size := by omega
  by_cases hcon : 4 * (T.num - 1) < T.slots.size
  · have hslots : (tableDelete T).slots =
        T.slots.extract 0 (T.num - 1) ++
          Array.replicate (T.slots.size / 2 - (T.num - 1)) none := by
      unfold tableDelete
      rw [dite_eq_right hnum, dite_eq_left hcon]
    have hsize : (tableDelete T).slots.size = T.slots.size / 2 := by
      rw [tableDelete_size]
      simp [hnum, hcon]
    rw [hsize, hslots]
  · have hset : T.num - 1 < T.slots.size := by omega
    have hslots : (tableDelete T).slots = T.slots.set (T.num - 1) none hset := by
      unfold tableDelete
      rw [dite_eq_right hnum, dite_eq_right hcon]
    have hsize : (tableDelete T).slots.size = T.slots.size := by
      rw [tableDelete_size]
      simp [hnum, hcon]
    rw [hsize, hslots]
    apply Array.ext
    · simp only [Array.size_set, Array.size_append, Array.size_replicate,
        extract_size_of_le T.slots hkle]
      omega
    · intro i hi _
      have hisize : i < T.slots.size := by simpa only [Array.size_set] using hi
      by_cases hlt : i < T.num - 1
      · have hne : T.num - 1 ≠ i := by omega
        have hpre : i < (T.slots.extract 0 (T.num - 1)).size := by
          rw [extract_size_of_le _ hkle]
          exact hlt
        have hleft : (T.slots.set (T.num - 1) none hset)[i]'hi =
            T.slots[i]'hisize := by
          rw [Array.getElem_set]
          exact ite_eq_right hne
        rw [hleft, Array.getElem_append_left hpre, Array.getElem_extract]
        simp only [Nat.zero_add]
      · by_cases heq : i = T.num - 1
        · subst i
          have hpre : (T.slots.extract 0 (T.num - 1)).size ≤ T.num - 1 := by
            have h := extract_size_of_le T.slots hkle
            omega
          have hleft : (T.slots.set (T.num - 1) none hset)[T.num - 1]'hi = none := by
            rw [Array.getElem_set]
            exact ite_eq_left rfl
          rw [hleft, Array.getElem_append_right hpre, Array.getElem_replicate]
        · have hne : T.num - 1 ≠ i := by omega
          have hpre : (T.slots.extract 0 (T.num - 1)).size ≤ i := by
            rw [extract_size_of_le _ hkle]
            omega
          have hnone : ∀ h : i < T.slots.size, T.slots[i] = none := by
            intro h
            cases hval : T.slots[i] with
            | none => rfl
            | some _ =>
              have hlt' : i < T.num := (wellFormed_apply hT i h).mp (by simp [hval])
              exfalso
              omega
          have hleft : (T.slots.set (T.num - 1) none hset)[i]'hi =
              T.slots[i]'hisize := by
            rw [Array.getElem_set]
            exact ite_eq_right hne
          rw [hleft, hnone, Array.getElem_append_right hpre,
            Array.getElem_replicate]

/-- Deletion preserves exact compact-prefix occupancy. -/
public theorem tableDelete_wellFormed {α : Type u} (T : Table α)
    (hT : WellFormed T) : WellFormed (tableDelete T) := by
  by_cases h0 : T.num = 0
  · have hdel : tableDelete T = T := by simp [tableDelete, h0]
    rwa [hdel]
  · exact wellFormed_of_slots T _ _ _ hT (tableDelete_num T) (by omega)
      (tableDelete_slots T hT h0)

/-- Deletion removes exactly the last logical item from the contents. -/
public theorem tableDelete_contents {α : Type u} (T : Table α) (hT : WellFormed T) :
    (contents (tableDelete T)).toList = (contents T).toList.dropLast := by
  by_cases h0 : T.num = 0
  · have hdel : tableDelete T = T := by simp [tableDelete, h0]
    have hcontents : contents T = #[] := by
      rw [contents_eq, h0]
      simp
    simp [hdel, hcontents]
  · have hkle : T.num - 1 ≤ T.slots.size := by have h := T.num_le; omega
    have hdel_contents : contents (tableDelete T) =
        (T.slots.extract 0 (T.num - 1)).filterMap id := by
      rw [contents_eq, tableDelete_num, tableDelete_slots T hT h0,
        extract_append_prefix _ _ hkle]
    have hlt : T.num - 1 < T.slots.size := by have h := T.num_le; omega
    obtain ⟨x, hx⟩ : ∃ x, T.slots[T.num - 1]'hlt = some x := by
      have hsome : (T.slots[T.num - 1]'hlt).isSome = true :=
        (wellFormed_apply hT _ hlt).mpr (by omega)
      cases hval : T.slots[T.num - 1]'hlt with
      | none => simp [hval] at hsome
      | some x => exact ⟨x, rfl⟩
    have hcontents : contents T =
        ((T.slots.extract 0 (T.num - 1)).filterMap id).push x := by
      rw [contents_eq, extract_num_push T h0, hx]
      exact Array.filterMap_push_some (f := id) rfl (by simp only [Array.size_push])
    rw [hdel_contents, hcontents, Array.toList_push]
    simp

/-- Lookup below the deleted position is unchanged by deletion. -/
public theorem get?_delete_of_lt {α : Type u} (T : Table α) (hT : WellFormed T)
    {i : Nat} (hi : i < T.num - 1) : get? (tableDelete T) i = get? T i := by
  have hnum : T.num ≠ 0 := by omega
  have hdel_num := tableDelete_num T
  have hiDel : i < (tableDelete T).num := by omega
  have hiT : i < T.num := by omega
  have hkle : T.num - 1 ≤ T.slots.size := by have h := T.num_le; omega
  have hpre : i < (T.slots.extract 0 (T.num - 1)).size := by
    rw [extract_size_of_le _ hkle]
    exact hi
  have e1 : get? (tableDelete T) i = ((tableDelete T).slots[i]?).bind id := by
    simp [get?, hiDel]
  have e2 : get? T i = (T.slots[i]?).bind id := by simp [get?, hiT]
  rw [e1, e2, tableDelete_slots T hT hnum]
  simp only [Array.getElem?_append, Array.getElem?_extract, Nat.min_eq_left hkle,
    Nat.sub_zero, Nat.zero_add, hpre, hi, ↓reduceIte]

/-- Lookup at the deleted position finds nothing after deletion. -/
public theorem get?_delete_last {α : Type u} (T : Table α) :
    get? (tableDelete T) (T.num - 1) = none := by
  have h := tableDelete_num T
  exact get?_eq_none_of_le _ (by omega)

end Cslib.Algorithms.Lean.DynamicTable
