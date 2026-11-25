/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Init.Data.Array.Lemmas
public import Mathlib.Algebra.Group.Nat.Defs
import Batteries.Data.Array.Lemmas

/-!
# Dynamic-table insertion

CLRS, fourth edition, Section 16.4.1, printed pages 461–464. Count one event
for each copied old item and for the new item write, not allocation or full RAM cost.
Retained Lean is authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.DynamicTable

/-- **Dynamic table.** A dynamic table with items of type $\alpha$ consists of an array of slots
$s_0, \dots, s_{m-1}$, each either empty or holding an item of type $\alpha$, together with an
item count $n$ satisfying $n \le m$. The number $m$ of slots is the capacity of the table. -/
public structure Table (α : Type u) where
  slots : Array (Option α)
  num : Nat
  num_le : num ≤ slots.size

/-- **Well-formed dynamic table.** A dynamic table with slots $s_0, \dots, s_{m-1}$ and item count
$n$ is well formed when, for every $i < m$, slot $s_i$ is occupied if and only if $i < n$; that is,
the occupied slots are exactly the first $n$.

The items held in the occupied slots are not constrained. -/
public def WellFormed {α : Type u} (T : Table α) : Prop :=
  ∀ (i : Nat) (h : i < T.slots.size), (T.slots[i]).isSome ↔ i < T.num

/-- **Characterization of well-formed dynamic tables.** A dynamic table with slots
$s_0, \dots, s_{m-1}$ and item count $n$ is well formed if and only if, for every $i < m$, slot
$s_i$ is occupied exactly when $i < n$. -/
public theorem wellFormed_iff {α : Type u} (T : Table α) :
    WellFormed T ↔
      ∀ (i : Nat) (h : i < T.slots.size), (T.slots[i]).isSome ↔ i < T.num :=
  Iff.rfl

/-- **Contents of a dynamic table.** Let $T$ be a dynamic table with slots $s_0, \dots, s_{m-1}$,
each empty or holding an item, and item count $n \le m$. The contents of $T$ is the array of the
items held by the occupied slots among $s_0, \dots, s_{n-1}$, in order; empty slots in this
prefix are skipped.

The insertion procedure never consults the contents. -/
public def contents {α : Type u} (T : Table α) : Array α :=
  (T.slots.extract 0 T.num).filterMap id

private lemma contents_eq_internal {α : Type u} (T : Table α) :
    contents T = (T.slots.extract 0 T.num).filterMap id :=
  rfl

/-- **Formula for the contents of a dynamic table.** Let $T$ be a dynamic table with slots
$s_0, \dots, s_{m-1}$, each empty or holding an item, and item count $n \le m$. The contents of
$T$ is the array obtained from the prefix $s_0, \dots, s_{n-1}$ by skipping the empty slots and
keeping the items of the occupied ones, in order. -/
public theorem contents_eq {α : Type u} (T : Table α) :
    contents T = (T.slots.extract 0 T.num).filterMap id :=
  contents_eq_internal T

/-- **Empty dynamic table.** The empty dynamic table is the table with no slots (capacity $0$)
and item count $0$. It models a table before its first allocation. -/
public def empty {α : Type u} : Table α := ⟨#[], 0, by simp⟩

private lemma empty_eq_internal {α : Type u} :
    (empty : Table α) = ⟨#[], 0, by simp⟩ :=
  rfl

/-- **The empty dynamic table has no slots and no items.** The empty dynamic table has an empty
slot array, so capacity $0$, and item count $0$. -/
public theorem empty_eq {α : Type u} :
    (empty : Table α) = ⟨#[], 0, by simp⟩ :=
  empty_eq_internal

@[no_expose] private def copyItems {α : Type u} (values : List (Option α))
    (slots : Array (Option α)) (i : Nat) (bound : i + values.length ≤ slots.size) :
    TimeM Nat {out : Array (Option α) // out.size = slots.size} :=
  match values with
  | [] => pure ⟨slots, rfl⟩
  | value :: values => do
    have hi : i < slots.size := by simp only [List.length_cons] at bound; omega
    TimeM.tick 1
    let next ← copyItems values (slots.set i value hi) (i + 1) (by
      simp only [Array.size_set, List.length_cons] at bound ⊢
      omega)
    pure ⟨next.val, by simpa only [Array.size_set] using next.property⟩

private lemma copyItems_time {α : Type u} (values : List (Option α))
    (slots : Array (Option α)) (i : Nat) (bound : i + values.length ≤ slots.size) :
    (copyItems values slots i bound).time = values.length := by
  induction values generalizing slots i with
  | nil => simp [copyItems]
  | cons value values ih =>
    simp only [copyItems, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
      ih, List.length_cons, Nat.add_zero]
    exact Nat.add_comm 1 values.length

private lemma copyItems_size {α : Type u} (values : List (Option α))
    (slots : Array (Option α)) (i : Nat) (bound : i + values.length ≤ slots.size) :
    (copyItems values slots i bound).ret.val.size = slots.size :=
  (copyItems values slots i bound).ret.property

private lemma set_after_prefix {α : Type u} (pre : List α) (a b : α) (n : Nat)
    (h : pre.length < (pre.toArray ++ Array.replicate (n + 1) b).size) :
    (pre.toArray ++ Array.replicate (n + 1) b).set pre.length a h =
      (pre ++ [a]).toArray ++ Array.replicate n b := by
  apply Array.toList_inj.mp
  simp only [List.size_toArray, Std.le_refl, Array.set_append_right, Nat.sub_self,
    Array.toList_append, Array.toList_set, Array.toList_replicate, List.replicate_succ,
    List.set_cons_zero, List.append_assoc, List.cons_append, List.nil_append]

private lemma set_after_array {α : Type u} (pre : Array α) (a b : α) (n : Nat)
    (h : pre.size < (pre ++ Array.replicate (n + 1) b).size) :
    (pre ++ Array.replicate (n + 1) b).set pre.size a h =
      pre ++ #[a] ++ Array.replicate n b := by
  apply Array.toList_inj.mp
  simp only [Std.le_refl, Array.set_append_right, Nat.sub_self,
    Array.toList_append, Array.toList_set, Array.toList_replicate,
    List.replicate_succ, List.set_cons_zero,
    List.append_assoc, List.cons_append, List.nil_append]

private lemma copyItems_congr {α : Type u} (values : List (Option α))
    (slots slots' : Array (Option α)) (i i' : Nat)
    (bound : i + values.length ≤ slots.size) (bound' : i' + values.length ≤ slots'.size)
    (hs : slots = slots') (hi : i = i') :
    (copyItems values slots i bound).ret.val =
      (copyItems values slots' i' bound').ret.val := by
  subst slots'
  subst i'
  rfl

private lemma copyItems_prefix {α : Type u} (values pre : List (Option α)) (n : Nat)
    (bound : pre.length + values.length ≤
      (pre.toArray ++ Array.replicate (values.length + n) none).size) :
    (copyItems values (pre.toArray ++ Array.replicate (values.length + n) none)
      pre.length bound).ret.val = (pre ++ values).toArray ++ Array.replicate n none := by
  induction values generalizing pre with
  | nil => simp only [copyItems, TimeM.ret_pure, List.length_nil, Nat.zero_add,
      List.append_nil]
  | cons value values ih =>
    simp only [copyItems, TimeM.ret_bind, TimeM.ret_pure]
    have hs :
        (pre.toArray ++ Array.replicate ((value :: values).length + n) none).set
          pre.length value (by simp only [Array.size_append, List.size_toArray,
            Array.size_replicate, List.length_cons]; omega) =
        (pre ++ [value]).toArray ++ Array.replicate (values.length + n) none := by
      simpa only [List.length_cons, Nat.add_right_comm] using
        set_after_prefix pre value none (values.length + n) (by
          simp only [Array.size_append, List.size_toArray, Array.size_replicate]
          omega)
    have nextBound : (pre ++ [value]).length + values.length ≤
        ((pre ++ [value]).toArray ++ Array.replicate (values.length + n) none).size := by
      simp only [Array.size_append, List.size_toArray, Array.size_replicate]
      omega
    calc
      _ = (copyItems values
          ((pre ++ [value]).toArray ++ Array.replicate (values.length + n) none)
          (pre ++ [value]).length nextBound).ret.val :=
        copyItems_congr values _ _ _ _ _ _ hs (by
          simp only [List.length_append, List.length_singleton])
      _ = (pre ++ value :: values).toArray ++ Array.replicate n none := by
        simpa only [List.append_assoc, List.singleton_append] using
          ih (pre ++ [value]) nextBound

private lemma copyItems_all {α : Type u} (slots : Array (Option α)) (n : Nat)
    (bound : 0 + slots.toList.length ≤ (Array.replicate (slots.size + n) none).size) :
    (copyItems slots.toList (Array.replicate (slots.size + n) none) 0 bound).ret.val =
      slots ++ Array.replicate n none := by
  have prefixBound : ([] : List (Option α)).length + slots.toList.length ≤
      (([] : List (Option α)).toArray ++
        Array.replicate (slots.toList.length + n) none).size := by
    simp only [List.length_nil, Nat.zero_add, Array.size_append, List.size_toArray,
      Array.size_replicate]
    omega
  calc
    _ = (copyItems slots.toList
        (([] : List (Option α)).toArray ++ Array.replicate (slots.toList.length + n) none)
        [].length prefixBound).ret.val :=
      copyItems_congr slots.toList _ _ _ _ _ _ (by
        simp only [Array.length_toList, Array.empty_append]) rfl
    _ = slots ++ Array.replicate n none := by
      simpa only [List.nil_append, Array.toArray_toList] using
        copyItems_prefix slots.toList [] n prefixBound

private lemma copyItems_double {α : Type u} (slots : Array (Option α))
    (bound : 0 + slots.toList.length ≤ (Array.replicate (2 * slots.size) none).size) :
    (copyItems slots.toList (Array.replicate (2 * slots.size) none) 0 bound).ret.val =
      slots ++ Array.replicate slots.size none := by
  have hb : 0 + slots.toList.length ≤
      (Array.replicate (slots.size + slots.size) (none : Option α)).size := by
    simp only [Nat.zero_add, Array.length_toList, Array.size_replicate]
    omega
  calc
    _ = (copyItems slots.toList (Array.replicate (slots.size + slots.size) none)
        0 hb).ret.val :=
      copyItems_congr slots.toList _ _ _ _ _ _ (by congr 1; omega) rfl
    _ = slots ++ Array.replicate slots.size none := copyItems_all slots slots.size hb

private lemma slots_decompose {α : Type u} (T : Table α) (hT : WellFormed T) :
    T.slots = T.slots.extract 0 T.num ++ Array.replicate (T.slots.size - T.num) none := by
  have hb := T.num_le
  have hp : (T.slots.extract 0 T.num).size = T.num := by
    simp only [Array.size_extract, Nat.min_eq_left T.num_le, Nat.sub_zero]
  apply Array.ext
  · simp only [Array.size_append, hp, Array.size_replicate]
    omega
  · intro i hi hj
    by_cases hn : i < T.num
    · have he : i < (T.slots.extract 0 T.num).size := by omega
      rw [Array.getElem_append_left he, Array.getElem_extract]
      simp only [Nat.zero_add]
    · have he : (T.slots.extract 0 T.num).size ≤ i := by omega
      rw [Array.getElem_append_right he, Array.getElem_replicate]
      cases hv : T.slots[i] with
      | none => rfl
      | some value =>
        have hf := (hT i hi).mp (by simp only [hv, Option.isSome_some])
        omega

@[no_expose] private def initialTable {α : Type u} (T : Table α) : Table α :=
  if hz : T.slots.size = 0 then
    ⟨Array.replicate 1 none, T.num, by
      have h := T.num_le
      simp only [hz] at h
      simp only [Array.size_replicate]
      omega⟩
  else T

private lemma initialTable_pos {α : Type u} (T : Table α) :
    0 < (initialTable T).slots.size := by
  by_cases hz : T.slots.size = 0
  · simp [initialTable, hz]
  · have hp : 0 < T.slots.size := by omega
    simpa [initialTable, hz] using hp

/-- **TABLE-INSERT.** Let $T$ be a dynamic table with slots $s_0, \dots, s_{m-1}$ and item count
$n \le m$, and let $x$ be an item. Inserting $x$ into $T$ proceeds as follows. If $m = 0$, first
replace the slots by a single empty slot. Then, if the table is full, that is, $n$ equals the
current capacity $c$, allocate $2c$ empty slots and copy the $c$ old slots into the first $c$ of
them, at cost $1$ per copied slot. Finally write $x$ into slot $n$, at cost $1$, and set the item
count to $n + 1$. The result is the new table together with the total cost. -/
public def tableInsert {α : Type u} (T : Table α) (x : α) : TimeM Nat (Table α) := do
  let initial := initialTable T
  if hf : initial.num = initial.slots.size then
    let copied ← copyItems initial.slots.toList
      (Array.replicate (2 * initial.slots.size) none) 0 (by simp; omega)
    have hw : initial.num < copied.val.size := by
      rw [copied.property]
      simp only [Array.size_replicate]
      have hp : 0 < initial.slots.size := initialTable_pos T
      omega
    TimeM.tick 1
    pure ⟨copied.val.set initial.num (some x) hw, initial.num + 1, by
      simp only [Array.size_set]
      omega⟩
  else
    have hw : initial.num < initial.slots.size := by
      have hn := initial.num_le
      omega
    TimeM.tick 1
    pure ⟨initial.slots.set initial.num (some x) hw, initial.num + 1, by
      simp only [Array.size_set]
      omega⟩

/-- **Inserting an array of items into a dynamic table.** Given a dynamic table $T$ and an array
$x_0, \dots, x_{k-1}$ of items, the result of inserting the array into $T$ is obtained by starting
from $T$ and inserting $x_0, x_1, \dots, x_{k-1}$ one at a time with TABLE-INSERT, in array
order. Its cost is the sum of the costs of the $k$ insertions; for an empty array the result is
$T$ at cost $0$. -/
public def tableInsertMany {α : Type u} (T : Table α) (xs : Array α) :
    TimeM Nat (Table α) :=
  xs.foldlM (fun t x => tableInsert t x) T

/-- **Insertion increases the item count by one.** For every dynamic table $T$ with item count $n$
and every item $x$, the table returned by inserting $x$ into $T$ with TABLE-INSERT has item count
$n + 1$. -/
public theorem tableInsert_num {α : Type u} (T : Table α) (x : α) :
    (tableInsert T x).ret.num = T.num + 1 := by
  have hn : (initialTable T).num = T.num := by
    unfold initialTable
    split <;> rfl
  unfold tableInsert
  dsimp only
  split <;> simpa only [TimeM.ret_bind, TimeM.ret_pure] using
    congrArg (fun n => n + 1) hn

/-- **Capacity after an insertion.** Let $T$ be a dynamic table with item count $n$ and capacity
(number of slots) $m$, and let $x$ be an item. The table returned by inserting $x$ into $T$ with
TABLE-INSERT has capacity $1$ if $m = 0$, capacity $2m$ if $m > 0$ and $n = m$, and capacity $m$
otherwise. -/
public theorem tableInsert_size {α : Type u} (T : Table α) (x : α) :
    (tableInsert T x).ret.slots.size =
      if T.slots.size = 0 then 1
      else if T.num = T.slots.size then 2 * T.slots.size else T.slots.size := by
  by_cases hz : T.slots.size = 0
  · have hn : T.num = 0 := by have h := T.num_le; omega
    simp only [tableInsert, initialTable, hz, hn, ↓reduceDIte, ↓reduceIte,
      Array.size_replicate,
      Nat.reduceEqDiff, TimeM.ret_bind, TimeM.ret_pure, Array.size_set]
  · by_cases hf : T.num = T.slots.size
    · simp only [tableInsert, initialTable, hz, hf, ↓reduceDIte, ↓reduceIte, TimeM.ret_bind,
        TimeM.ret_pure, Array.size_set, copyItems_size, Array.size_replicate]
    · simp only [tableInsert, initialTable, hz, hf, ↓reduceDIte, ↓reduceIte, TimeM.ret_bind,
        TimeM.ret_pure, Array.size_set]

/-- **Cost of an insertion.** Let $T$ be a dynamic table with item count $n$ and capacity $m$, and
let $x$ be an item. Inserting $x$ into $T$ with TABLE-INSERT costs $1 + n$ if $m > 0$ and $n = m$,
and costs $1$ otherwise. -/
public theorem tableInsert_time {α : Type u} (T : Table α) (x : α) :
    (tableInsert T x).time =
      1 + if T.slots.size > 0 ∧ T.num = T.slots.size then T.num else 0 := by
  by_cases hz : T.slots.size = 0
  · have hn : T.num = 0 := by have h := T.num_le; omega
    simp only [tableInsert, initialTable, hz, hn, ↓reduceDIte, Array.size_replicate,
      Nat.reduceEqDiff, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
    simp only [Nat.lt_irrefl, false_and, ↓reduceIte, Nat.add_zero]
  · have hp : 0 < T.slots.size := by omega
    by_cases hf : T.num = T.slots.size
    · simp only [tableInsert, initialTable, hz, hf, hp, ↓reduceDIte,
        TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, copyItems_time,
        Array.length_toList, Nat.add_zero, and_self, ↓reduceIte]
      exact Nat.add_comm T.slots.size 1
    · simp only [tableInsert, initialTable, hz, hf, hp, ↓reduceDIte,
        TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, and_false, ↓reduceIte,
        Nat.add_zero]

/-- **Amortized cost of dynamic-table insertion.** For a dynamic table $T$ with item count $n$
and capacity (number of slots) $m$, let $\Phi(T) = 2n - m$, an integer that may be negative.
If inserting an item $x$ into $T$ has cost $c$ and returns the table $T'$, then
$c + \Phi(T') - \Phi(T) \le 3$. Here the cost of an insertion is one unit for writing $x$ plus
one unit for each old slot copied when a full table is doubled. -/
public theorem tableInsert_amortized {α : Type u} (T : Table α) (x : α) :
    ((tableInsert T x).time : Int) +
      (2 * ((tableInsert T x).ret.num : Int) - ((tableInsert T x).ret.slots.size : Int)) -
      (2 * (T.num : Int) - (T.slots.size : Int)) ≤ 3 := by
  rw [tableInsert_time, tableInsert_num, tableInsert_size]
  by_cases hz : T.slots.size = 0
  · have hn : T.num = 0 := by have h := T.num_le; omega
    simp only [hz, hn, Nat.lt_irrefl, false_and, ↓reduceIte]
    omega
  · have hp : 0 < T.slots.size := by omega
    by_cases hf : T.num = T.slots.size
    · simp only [hz, hf, hp, and_self, ↓reduceIte]
      omega
    · simp only [hz, hf, hp, and_false, ↓reduceIte]
      omega

/-- **Slots after an insertion.** Let $T$ be a well-formed dynamic table with slots
$s_0, \dots, s_{m-1}$ and item count $n$, let $x$ be an item, and let $T'$ be the table returned
by inserting $x$ into $T$ with TABLE-INSERT, with capacity $m'$. Then the slots of $T'$ are
$s_0, \dots, s_{n-1}$, followed by a slot holding $x$, followed by $m' - (n + 1)$ empty slots. -/
public theorem tableInsert_slots {α : Type u} (T : Table α) (x : α) :
    WellFormed T → (tableInsert T x).ret.slots =
      T.slots.extract 0 T.num ++ #[some x] ++
        Array.replicate ((tableInsert T x).ret.slots.size - (T.num + 1)) none := by
  intro hT
  rw [tableInsert_size]
  by_cases hz : T.slots.size = 0
  · have hn : T.num = 0 := by have h := T.num_le; omega
    apply Array.toList_inj.mp
    simp only [tableInsert, initialTable, hz, hn, ↓reduceDIte, ↓reduceIte,
      Array.size_replicate, Nat.reduceEqDiff, TimeM.ret_bind, TimeM.ret_pure,
      Array.toList_set, Array.toList_replicate, List.replicate_succ,
      List.replicate_zero, List.set_cons_zero, Array.extract_zero,
      Array.toList_append, Nat.reduceAdd, Nat.sub_self, List.append_nil,
      List.nil_append]
  · have hp : 0 < T.slots.size := by omega
    by_cases hf : T.num = T.slots.size
    · have hc : T.slots.size = (T.slots.size - 1) + 1 := by omega
      have hd : 2 * T.slots.size - (T.slots.size + 1) = T.slots.size - 1 := by omega
      have hinit : initialTable T = T := by
        simp only [initialTable, hz, ↓reduceDIte]
      have hi : (initialTable T).slots.size = T.slots.size :=
        congrArg (fun t => t.slots.size) hinit
      have hb : 0 + T.slots.toList.length ≤
          (Array.replicate (2 * T.slots.size) (none : Option α)).size := by
        simp only [Nat.zero_add, Array.length_toList, Array.size_replicate]
        omega
      have hb' : 0 + T.slots.toList.length ≤
          (Array.replicate (2 * (initialTable T).slots.size) (none : Option α)).size := by
        simp only [Nat.zero_add, Array.length_toList, Array.size_replicate, hi]
        omega
      have hcopy : (copyItems T.slots.toList
          (Array.replicate (2 * (initialTable T).slots.size) none) 0 hb').ret.val =
          T.slots ++ Array.replicate T.slots.size none := by
        calc
          _ = (copyItems T.slots.toList
              (Array.replicate (2 * T.slots.size) none) 0 hb).ret.val :=
            copyItems_congr T.slots.toList _ _ _ _ _ _
              (congrArg (fun n => Array.replicate (2 * n) (none : Option α)) hi) rfl
          _ = T.slots ++ Array.replicate T.slots.size none := copyItems_double T.slots hb
      apply Array.toList_inj.mp
      simp only [tableInsert, hinit, hz, hf, ↓reduceDIte, ↓reduceIte,
        TimeM.ret_bind, TimeM.ret_pure, Array.toList_set,
        Array.extract_size, hd]
      rw [hcopy]
      simpa only [← hc, Array.toList_set] using congrArg Array.toList
        (set_after_array T.slots (some x) none (T.slots.size - 1) (by
          simp only [Array.size_append, Array.size_replicate]
          omega))
    · have hb := T.num_le
      have he : (T.slots.extract 0 T.num).size = T.num := by
        simp only [Array.size_extract, Nat.min_eq_left hb, Nat.sub_zero]
      have hg : T.slots.size - T.num = (T.slots.size - (T.num + 1)) + 1 := by omega
      have hs := set_after_array (T.slots.extract 0 T.num) (some x) none
        (T.slots.size - (T.num + 1)) (by
          simp only [Array.size_append, Array.size_replicate]
          omega)
      have hslots : T.slots.toList =
          (T.slots.extract 0 T.num ++
            Array.replicate ((T.slots.size - (T.num + 1)) + 1) none).toList := by
        rw [← hg]
        exact congrArg Array.toList (slots_decompose T hT)
      apply Array.toList_inj.mp
      simp only [tableInsert, initialTable, hz, hf, ↓reduceDIte, ↓reduceIte,
        TimeM.ret_bind, TimeM.ret_pure, Array.toList_set]
      rw [hslots]
      simpa only [Array.toList_set, he] using congrArg Array.toList hs

private lemma wellFormed_of_slots {α : Type u} (T out : Table α) (x : α) (n : Nat)
    (hT : WellFormed T) (hnum : out.num = T.num + 1)
    (hslots : out.slots = T.slots.extract 0 T.num ++ #[some x] ++ Array.replicate n none) :
    WellFormed out := by
  rcases out with ⟨slots, num, bound⟩
  dsimp only at hnum hslots
  subst num
  subst slots
  have hb := T.num_le
  have he : (T.slots.extract 0 T.num).size = T.num := by
    simp only [Array.size_extract, Nat.min_eq_left hb, Nat.sub_zero]
  have hf : (T.slots.extract 0 T.num ++ #[some x]).size = T.num + 1 := by
    simp only [Array.size_append, he, Array.size_singleton]
  intro i hi
  by_cases hn : i < T.num + 1
  · have hl : i < (T.slots.extract 0 T.num ++ #[some x]).size := by omega
    rw [Array.getElem_append_left hl]
    by_cases ho : i < T.num
    · have hp : i < (T.slots.extract 0 T.num).size := by omega
      rw [Array.getElem_append_left hp, Array.getElem_extract]
      simp only [Nat.zero_add]
      exact ⟨fun _ => hn, fun _ => (hT i (by omega)).mpr ho⟩
    · have hx : i = T.num := by omega
      subst i
      rw [Array.getElem_append_right (by omega)]
      simp only [he, Nat.sub_self]
      exact ⟨fun _ => hn, fun _ => rfl⟩
  · rw [Array.getElem_append_right (by omega), Array.getElem_replicate]
    exact ⟨fun h => Bool.noConfusion h, fun h => (hn h).elim⟩

/-- **Insertion preserves well-formedness.** If $T$ is a well-formed dynamic table and $x$ is an
item, then the table returned by inserting $x$ into $T$ with TABLE-INSERT is well formed. -/
public theorem tableInsert_wellFormed {α : Type u} (T : Table α) (x : α) :
    WellFormed T → WellFormed (tableInsert T x).ret := by
  intro hT
  exact wellFormed_of_slots T (tableInsert T x).ret x _ hT
    (tableInsert_num T x) (tableInsert_slots T x hT)

/-- **Insertion appends to the contents.** If $T$ is a well-formed dynamic table and $x$ is an
item, then the contents of the table obtained by inserting $x$ into $T$ are the contents of $T$
followed by $x$. -/
public theorem tableInsert_contents {α : Type u} (T : Table α) (x : α) :
    WellFormed T → contents (tableInsert T x).ret = (contents T).push x := by
  intro hT
  unfold contents
  rw [tableInsert_num, tableInsert_slots T x hT]
  have hb := T.num_le
  have hp : (T.slots.extract 0 T.num).size = T.num := by
    simp only [Array.size_extract, Nat.min_eq_left hb, Nat.sub_zero]
  rw [Array.extract_append_of_stop_le_size_left (by
    simp only [Array.size_append, hp, Array.size_singleton]; omega)]
  rw [show T.num + 1 = (T.slots.extract 0 T.num ++ #[some x]).size by
    simp only [Array.size_append, hp, Array.size_singleton]]
  rw [Array.extract_size, ← Array.push_eq_append]
  exact Array.filterMap_push_some (f := id) rfl (by simp only [Array.size_push])

/-- **Repeated insertion preserves well-formedness of a dynamic table.** Call a dynamic table
with item count $n$ well formed when, for every slot index $i$, slot $i$ is occupied exactly
when $i < n$. If a dynamic table $T$ is well formed, then for every array $xs$, the table
obtained from $T$ by inserting the entries of $xs$ one at a time with TABLE-INSERT, in array
order, is again well formed. -/
public theorem tableInsertMany_wellFormed {α : Type u} (T : Table α) (xs : Array α) :
    WellFormed T → WellFormed (tableInsertMany T xs).ret := by
  cases xs with
  | mk values =>
    unfold tableInsertMany
    rw [List.foldlM_toArray]
    intro hT
    induction values generalizing T with
    | nil => simpa only [List.foldlM_nil, TimeM.ret_pure] using hT
    | cons x values ih =>
      simp only [List.foldlM_cons, TimeM.ret_bind]
      exact ih (tableInsert T x).ret (tableInsert_wellFormed T x hT)

/-- **Inserting an array appends it to the contents.** If $T$ is a well-formed dynamic table
and $x_1, \dots, x_k$ is an array of items, then inserting $x_1, \dots, x_k$ into $T$ one at a
time, in this order, gives a table whose contents are the contents of $T$ followed by
$x_1, \dots, x_k$. -/
public theorem tableInsertMany_contents {α : Type u} (T : Table α) (xs : Array α) :
    WellFormed T → contents (tableInsertMany T xs).ret = contents T ++ xs := by
  cases xs with
  | mk values =>
    unfold tableInsertMany
    rw [List.foldlM_toArray]
    intro hT
    induction values generalizing T with
    | nil => simp only [List.foldlM_nil, TimeM.ret_pure, Array.append_empty]
    | cons x values ih =>
      simp only [List.foldlM_cons, TimeM.ret_bind]
      rw [ih _ (tableInsert_wellFormed T x hT), tableInsert_contents T x hT]
      rw [Array.push_eq_append, Array.append_assoc]
      apply congrArg (fun ys => contents T ++ ys)
      apply Array.toList_inj.mp
      simp only [Array.toList_append, List.cons_append, List.nil_append]

private lemma insert_load {α : Type u} (T : Table α) (x : α)
    (h : T.slots.size ≤ 2 * T.num) :
    (tableInsert T x).ret.slots.size ≤ 2 * (tableInsert T x).ret.num := by
  rw [tableInsert_num, tableInsert_size]
  by_cases hz : T.slots.size = 0
  · simp only [hz, ↓reduceIte]
    omega
  · by_cases hf : T.num = T.slots.size
    · simp only [hz, hf, ↓reduceIte]
      omega
    · simp only [hz, hf, ↓reduceIte]
      omega

private lemma fold_num {α : Type u} (values : List α) (T : Table α) :
    (values.foldlM (fun t x => tableInsert t x) T).ret.num = T.num + values.length := by
  induction values generalizing T with
  | nil => simp only [List.foldlM_nil, TimeM.ret_pure, List.length_nil, Nat.add_zero]
  | cons x values ih =>
    simp only [List.foldlM_cons, TimeM.ret_bind, ih, tableInsert_num, List.length_cons]
    omega

private lemma fold_load {α : Type u} (values : List α) (T : Table α)
    (h : T.slots.size ≤ 2 * T.num) :
    (values.foldlM (fun t x => tableInsert t x) T).ret.slots.size ≤
      2 * (values.foldlM (fun t x => tableInsert t x) T).ret.num := by
  induction values generalizing T with
  | nil => simpa only [List.foldlM_nil, TimeM.ret_pure] using h
  | cons x values ih =>
    simp only [List.foldlM_cons, TimeM.ret_bind]
    exact ih _ (insert_load T x h)

/-- **Capacity after inserting into the empty table.** Starting from the empty dynamic table
and inserting the items of an array of length $k$ one at a time, the resulting table has
capacity (number of slots) at most $2k$. -/
public theorem tableInsertMany_size_le {α : Type u} (xs : Array α) :
    (tableInsertMany empty xs).ret.slots.size ≤ 2 * xs.size := by
  cases xs with
  | mk values =>
    unfold tableInsertMany
    rw [List.foldlM_toArray]
    have h := fold_load values (empty : Table α) (by
      simp only [empty, Array.size_empty, Nat.mul_zero]
      exact Nat.le_refl 0)
    rw [fold_num] at h
    simpa only [empty, Nat.zero_add, List.size_toArray] using h

private lemma insert_pos {α : Type u} (T : Table α) (x : α) :
    0 < (tableInsert T x).ret.slots.size := by
  rw [tableInsert_size]
  by_cases hz : T.slots.size = 0
  · simp only [hz, ↓reduceIte]
    omega
  · by_cases hf : T.num = T.slots.size
    · simp only [hz, hf, ↓reduceIte]
      omega
    · simp only [hz, hf, ↓reduceIte]
      omega

private lemma insert_charge {α : Type u} (T : Table α) (x : α)
    (hp : 0 < T.slots.size) :
    ((tableInsert T x).time : Int) +
      (2 * ((tableInsert T x).ret.num : Int) - ((tableInsert T x).ret.slots.size : Int)) -
      (2 * (T.num : Int) - (T.slots.size : Int)) = 3 := by
  rw [tableInsert_time, tableInsert_num, tableInsert_size]
  have hz : T.slots.size ≠ 0 := by omega
  by_cases hf : T.num = T.slots.size
  · simp only [hz, hf, hp, and_self, ↓reduceIte]
    omega
  · simp only [hz, hf, hp, and_false, ↓reduceIte]
    omega

private lemma fold_charge {α : Type u} (values : List α) (T : Table α)
    (hp : 0 < T.slots.size) :
    ((values.foldlM (fun t x => tableInsert t x) T).time : Int) +
      (2 * ((values.foldlM (fun t x => tableInsert t x) T).ret.num : Int) -
        ((values.foldlM (fun t x => tableInsert t x) T).ret.slots.size : Int)) -
      (2 * (T.num : Int) - (T.slots.size : Int)) = 3 * (values.length : Int) := by
  induction values generalizing T with
  | nil =>
    simp only [List.foldlM_nil, TimeM.time_pure, TimeM.ret_pure, List.length_nil]
    omega
  | cons x values ih =>
    have hs := insert_charge T x hp
    have ht := ih (tableInsert T x).ret (insert_pos T x)
    simp only [List.foldlM_cons, TimeM.time_bind, TimeM.ret_bind, List.length_cons]
    omega

private lemma fold_empty_charge {α : Type u} (x : α) (values : List α) :
    (((x :: values).foldlM (fun t y => tableInsert t y) empty).time : Int) +
      (2 * (((x :: values).foldlM (fun t y => tableInsert t y) empty).ret.num : Int) -
        (((x :: values).foldlM (fun t y => tableInsert t y) empty).ret.slots.size : Int)) =
      3 * ((x :: values).length : Int) - 1 := by
  have h := fold_charge values (tableInsert empty x).ret (insert_pos empty x)
  have hn : (tableInsert (empty : Table α) x).ret.num = 1 := tableInsert_num empty x
  have hc : (tableInsert (empty : Table α) x).ret.slots.size = 1 := tableInsert_size empty x
  have ht : (tableInsert (empty : Table α) x).time = 1 := tableInsert_time empty x
  simp only [List.foldlM_cons, TimeM.time_bind, TimeM.ret_bind, List.length_cons]
  omega

private lemma fold_empty_time_lt {α : Type u} (x : α) (values : List α) :
    ((x :: values).foldlM (fun t y => tableInsert t y) empty).time <
      3 * (x :: values).length := by
  have ht := fold_empty_charge x values
  have hc := fold_load (x :: values) (empty : Table α) (by
    simp only [empty, Array.size_empty, Nat.mul_zero]
    exact Nat.le_refl 0)
  omega

/-- **Total cost of insertions into the empty table.** Starting from the empty dynamic table
and inserting the items of an array of length $k$ one at a time, the total cost is at most
$3k$, where each insertion costs one unit for writing the new item plus one unit for each old
slot copied when a full table is doubled. -/
public theorem tableInsertMany_time_le {α : Type u} (xs : Array α) :
    (tableInsertMany empty xs).time ≤ 3 * xs.size := by
  cases xs with
  | mk values =>
    unfold tableInsertMany
    rw [List.foldlM_toArray]
    cases values with
    | nil =>
      simp only [List.foldlM_nil, TimeM.time_pure, List.size_toArray,
        List.length_nil, Nat.mul_zero, Nat.le_refl]
    | cons x values =>
      simpa only [List.size_toArray] using Nat.le_of_lt (fold_empty_time_lt x values)

/-- **Strict cost bound for nonempty insertion sequences.** Starting from the empty dynamic
table and inserting the items of a nonempty array of length $k$ one at a time, the total cost
is less than $3k$.

The bound is strict because the first insertion, which allocates the first slot, has amortized
cost $2$ rather than $3$. -/
public theorem tableInsertMany_time_lt {α : Type u} (xs : Array α) :
    xs.size > 0 → (tableInsertMany empty xs).time < 3 * xs.size := by
  intro hp
  cases xs with
  | mk values =>
    unfold tableInsertMany
    rw [List.foldlM_toArray]
    cases values with
    | nil =>
      simp only [List.size_toArray, List.length_nil] at hp
      omega
    | cons x values =>
      simpa only [List.size_toArray] using fold_empty_time_lt x values

end Cslib.Algorithms.Lean.DynamicTable
