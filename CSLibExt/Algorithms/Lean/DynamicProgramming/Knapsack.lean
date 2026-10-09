/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Zero-one knapsack

This module verifies capacity-indexed bottom-up dynamic programming for zero-one knapsack with
natural weights and values. The result records a finite set of bounded original item indices and
its optimum value. Each item is used at most once because every new table row reads only the
previous row, including for zero-weight items. Equal include/exclude values exclude the current,
later-indexed item.

The abstract cost model charges one unit for every item/capacity table cell and one unit for every
item row inspected during reconstruction. The exact cost is `n * (W + 1) + n`; for positive
capacity this is `O(nW)`. This bound is pseudo-polynomial: it is polynomial in the numeric capacity
`W`, whose binary encoding has length proportional to `log W`.

The recurrence follows Dasgupta, Papadimitriou, and Vazirani, *Algorithms*, Section 6.4. Returning
bounded finite indices is an explicit refinement of the source's optimum-value presentation.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM.Knapsack

/-- A zero-one knapsack item with a natural weight and value. -/
structure Item where
  /-- Weight consumed when the item is selected. -/
  weight : Nat
  /-- Value contributed when the item is selected. -/
  value : Nat
deriving DecidableEq, Repr

/-- A knapsack result. `Finset` gives distinct indices and `Fin` keeps them in range. -/
structure Result (items : List Item) where
  /-- Selected original item indices. -/
  chosen : Finset (Fin items.length)
  /-- Reported total value. -/
  value : Nat
deriving DecidableEq

/-- Total weight of the items at the selected indices. -/
def totalWeight (items : List Item) (chosen : Finset (Fin items.length)) : Nat :=
  chosen.sum fun i => (items.get i).weight

/-- Total value of the items at the selected indices. -/
def totalValue (items : List Item) (chosen : Finset (Fin items.length)) : Nat :=
  chosen.sum fun i => (items.get i).value

/-- A selected set is feasible when its total weight does not exceed the capacity. -/
def Feasible (items : List Item) (capacity : Nat)
    (chosen : Finset (Fin items.length)) : Prop :=
  totalWeight items chosen ≤ capacity

private def Within {items : List Item} (chosen : Finset (Fin items.length)) (i : Nat) : Prop :=
  ∀ j ∈ chosen, j.val < i

private def CellOptimal (items : List Item) (i capacity value : Nat) : Prop :=
  (∃ chosen : Finset (Fin items.length),
      Within chosen i ∧ Feasible items capacity chosen ∧ totalValue items chosen = value) ∧
    ∀ chosen : Finset (Fin items.length),
      Within chosen i → Feasible items capacity chosen → totalValue items chosen ≤ value

private theorem within_zero_eq_empty {items : List Item}
    {chosen : Finset (Fin items.length)} (h : Within chosen 0) : chosen = ∅ := by
  ext j
  constructor
  · intro hj
    exact (Nat.not_lt_zero _ (h j hj)).elim
  · simp

private theorem optimal_zero (items : List Item) (capacity : Nat) :
    CellOptimal items 0 capacity 0 := by
  constructor
  · refine ⟨∅, ?_, ?_, ?_⟩
    · simp [Within]
    · simp [Feasible, totalWeight]
    · simp [totalValue]
  · intro chosen hwithin _
    rw [within_zero_eq_empty hwithin]
    simp [totalValue]

private theorem totalWeight_erase_add (items : List Item)
    (chosen : Finset (Fin items.length)) (i : Fin items.length) (hi : i ∈ chosen) :
    totalWeight items (chosen.erase i) + (items.get i).weight = totalWeight items chosen := by
  simpa only [totalWeight] using
    Finset.sum_erase_add chosen (fun j => (items.get j).weight) hi

private theorem totalValue_erase_add (items : List Item)
    (chosen : Finset (Fin items.length)) (i : Fin items.length) (hi : i ∈ chosen) :
    totalValue items (chosen.erase i) + (items.get i).value = totalValue items chosen := by
  simpa only [totalValue] using
    Finset.sum_erase_add chosen (fun j => (items.get j).value) hi

private theorem totalWeight_insert (items : List Item)
    (chosen : Finset (Fin items.length)) (i : Fin items.length) (hi : i ∉ chosen) :
    totalWeight items (insert i chosen) = (items.get i).weight + totalWeight items chosen := by
  simpa only [totalWeight] using
    Finset.sum_insert (s := chosen) (a := i) (f := fun j => (items.get j).weight) hi

private theorem totalValue_insert (items : List Item)
    (chosen : Finset (Fin items.length)) (i : Fin items.length) (hi : i ∉ chosen) :
    totalValue items (insert i chosen) = (items.get i).value + totalValue items chosen := by
  simpa only [totalValue] using
    Finset.sum_insert (s := chosen) (a := i) (f := fun j => (items.get j).value) hi

private theorem within_erase {items : List Item} {chosen : Finset (Fin items.length)}
    {i : Nat} (h : Within chosen i) (j : Fin items.length) : Within (chosen.erase j) i := by
  intro k hk
  exact h k (Finset.mem_of_mem_erase hk)

private theorem not_mem_of_within {items : List Item} {chosen : Finset (Fin items.length)}
    {i : Nat} (h : Within chosen i) (j : Fin items.length) (hj : i ≤ j.val) : j ∉ chosen := by
  intro hmem
  exact (Nat.not_lt_of_ge hj) (h j hmem)

private theorem within_insert {items : List Item} {chosen : Finset (Fin items.length)}
    {i : Nat} (h : Within chosen i) (j : Fin items.length) (hj : j.val = i) :
    Within (insert j chosen) (i + 1) := by
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · omega
  · exact (h k hk).trans (Nat.lt_succ_self i)

private theorem within_mono {items : List Item} {chosen : Finset (Fin items.length)}
    {i j : Nat} (h : Within chosen i) (hij : i ≤ j) : Within chosen j := by
  intro k hk
  exact (h k hk).trans_le hij

private theorem within_of_succ_of_not_mem {items : List Item}
    {chosen : Finset (Fin items.length)} {i : Nat} (idx : Fin items.length)
    (hidx : idx.val = i) (hwithin : Within chosen (i + 1)) (hnot : idx ∉ chosen) :
    Within chosen i := by
  intro j hj
  have hjlt := hwithin j hj
  have hjle : j.val ≤ i := by omega
  apply Nat.lt_of_le_of_ne hjle
  intro heq
  have : j = idx := Fin.ext (heq.trans hidx.symm)
  exact hnot (this ▸ hj)

private theorem optimal_step (items : List Item) (i capacity : Nat) (hi : i < items.length)
    (without previous : Nat)
    (hout : CellOptimal items i capacity without)
    (hin : CellOptimal items i (capacity - (items.get ⟨i, hi⟩).weight) previous) :
    CellOptimal items (i + 1) capacity
      (if (items.get ⟨i, hi⟩).weight ≤ capacity then
        max without (previous + (items.get ⟨i, hi⟩).value)
      else without) := by
  let idx : Fin items.length := ⟨i, hi⟩
  change CellOptimal items (i + 1) capacity
    (if (items.get idx).weight ≤ capacity then
      max without (previous + (items.get idx).value) else without)
  change CellOptimal items i (capacity - (items.get idx).weight) previous at hin
  by_cases hfit : (items.get idx).weight ≤ capacity
  · simp only [hfit, ↓reduceIte]
    obtain ⟨⟨withoutSet, hwWithin, hwFeasible, hwValue⟩, hwBound⟩ := hout
    obtain ⟨⟨withSet, hiWithin, hiFeasible, hiValue⟩, hiBound⟩ := hin
    constructor
    · by_cases hbetter : without < previous + (items.get idx).value
      · have hnot : idx ∉ withSet := not_mem_of_within hiWithin idx (by simp [idx])
        refine ⟨insert idx withSet, within_insert hiWithin idx (by simp [idx]), ?_, ?_⟩
        · rw [Feasible, totalWeight_insert items withSet idx hnot]
          rw [Feasible] at hiFeasible
          omega
        · rw [totalValue_insert items withSet idx hnot, hiValue]
          omega
      · refine ⟨withoutSet, within_mono hwWithin (Nat.le_succ i), hwFeasible, ?_⟩
        omega
    · intro chosen hwithin hfeasible
      by_cases hmem : idx ∈ chosen
      · have heraseWithin : Within (chosen.erase idx) i :=
          within_of_succ_of_not_mem idx (by simp [idx]) (within_erase hwithin idx) (by simp)
        have hweight := totalWeight_erase_add items chosen idx hmem
        have heraseFeasible : Feasible items (capacity - (items.get idx).weight)
            (chosen.erase idx) := by
          rw [Feasible] at hfeasible ⊢
          omega
        have hvalue := totalValue_erase_add items chosen idx hmem
        have hbound := hiBound (chosen.erase idx) heraseWithin heraseFeasible
        omega
      · have hsmall := within_of_succ_of_not_mem idx (by simp [idx]) hwithin hmem
        exact (hwBound chosen hsmall hfeasible).trans (Nat.le_max_left _ _)
  · simp only [hfit, ↓reduceIte]
    constructor
    · obtain ⟨chosen, hwithin, hfeasible, hvalue⟩ := hout.1
      exact ⟨chosen, within_mono hwithin (Nat.le_succ i), hfeasible, hvalue⟩
    · intro chosen hwithin hfeasible
      have hnot : idx ∉ chosen := by
        intro hmem
        have hweight := totalWeight_erase_add items chosen idx hmem
        rw [Feasible] at hfeasible
        omega
      exact hout.2 chosen (within_of_succ_of_not_mem idx (by simp [idx]) hwithin hnot)
        hfeasible

private theorem optimal_unique {items : List Item} {i capacity a b : Nat}
    (ha : CellOptimal items i capacity a) (hb : CellOptimal items i capacity b) : a = b := by
  obtain ⟨chosenA, hwithinA, hfeasibleA, hvalueA⟩ := ha.1
  obtain ⟨chosenB, hwithinB, hfeasibleB, hvalueB⟩ := hb.1
  have hab := hb.2 chosenA hwithinA hfeasibleA
  have hba := ha.2 chosenB hwithinB hfeasibleB
  omega

/-- Bottom-up zero-one knapsack with one tick per table cell and reconstructed item row. -/
def solve (items : List Item) (capacity : Nat) : TimeM Nat (Result items) :=
  let Row (n : Nat) := Subtype (fun row : Array Nat => row.size = n + 1)
  let rec @[reducible] buildRow (item : Item) (up : Row capacity) :
      (c : Nat) → c ≤ capacity → TimeM Nat (Row c)
    | 0, _ => do
        TimeM.tick 1
        let without := up.1[0]'(by rw [up.2]; omega)
        let value := if item.weight ≤ 0 then
          max without (up.1[0 - item.weight]'(by rw [up.2]; omega) + item.value)
        else
          without
        pure ⟨#[value], by simp⟩
    | c + 1, hc => do
        let row ← buildRow item up c (by omega)
        TimeM.tick 1
        let without := up.1[c + 1]'(by rw [up.2]; omega)
        let value := if item.weight ≤ c + 1 then
          max without (up.1[c + 1 - item.weight]'(by rw [up.2]; omega) + item.value)
        else
          without
        pure ⟨row.1.push value, by simp [row.2]⟩
  let Table (m : Nat) := Subtype (fun data : Array (Array Nat) =>
    data.size = m + 1 ∧ ∀ i (hi : i < data.size), data[i].size = capacity + 1)
  let cell {m : Nat} (table : Table m) (i c : Nat) (hi : i ≤ m) (hc : c ≤ capacity) : Nat :=
    (table.1[i]'(by rw [table.2.1]; omega))[c]'(by rw [table.2.2]; omega)
  let rec @[reducible] buildTable (values : Array Item) :
      (i : Nat) → i ≤ values.size → TimeM Nat (Table i)
    | 0, _ => pure ⟨#[Array.replicate (capacity + 1) 0], by simp, by
        intro i hi
        have : i = 0 := by simpa using hi
        subst i
        simp⟩
    | i + 1, hi => do
        let table ← buildTable values i (by omega)
        let up : Row capacity :=
          ⟨table.1[i]'(by rw [table.2.1]; omega),
            table.2.2 i (by rw [table.2.1]; omega)⟩
        let row ← buildRow (values[i]'(by omega)) up capacity (by omega)
        pure ⟨table.1.push row.1, by simp [table.2.1], by
          intro k hk
          rw [Array.getElem_push]
          split
          · exact table.2.2 _ _
          · exact row.2⟩
  let rec @[reducible] reconstruct (values : Array Item) (hvalues : values.size = items.length)
      (table : Table values.size) :
      (i c : Nat) → i ≤ values.size → c ≤ capacity →
        TimeM Nat (Finset (Fin items.length))
    | 0, _, _, _ => pure ∅
    | i + 1, c, hi, hc => do
        TimeM.tick 1
        if cell table (i + 1) c hi hc = cell table i c (by omega) hc then
          reconstruct values hvalues table i c (by omega) hc
        else
          return insert ⟨i, by omega⟩
            (← reconstruct values hvalues table i (c - values[i].weight) (by omega) (by omega))
  let values := items.toArray
  do
    let table ← buildTable values values.size (by omega)
    let chosen ← reconstruct values (by simp [values]) table values.size capacity
      (by omega) (by omega)
    pure {
      chosen := chosen
      value := cell table values.size capacity (by omega) (by omega) }

private abbrev Row (n : Nat) := Subtype (fun row : Array Nat => row.size = n + 1)

private abbrev Table (capacity m : Nat) := Subtype (fun data : Array (Array Nat) =>
  data.size = m + 1 ∧ ∀ i (hi : i < data.size), data[i].size = capacity + 1)

private abbrev cell {capacity m : Nat} (table : Table capacity m)
    (i c : Nat) (hi : i ≤ m) (hc : c ≤ capacity) : Nat :=
  (table.1[i]'(by rw [table.2.1]; omega))[c]'(by rw [table.2.2]; omega)

private theorem buildRow_correct (items : List Item) (i : Nat) (hi : i < items.length)
    (capacity : Nat) (up : Row capacity)
    (hu : ∀ c (hc : c ≤ capacity),
      CellOptimal items i c (up.1[c]'(by rw [up.2]; omega)))
    (j : Nat) (hj : j ≤ capacity) :
    ∀ c (hc : c ≤ j), CellOptimal items (i + 1) c
      ((solve.buildRow capacity (items.get ⟨i, hi⟩) up j hj).ret.1[c]'(by
        rw [(solve.buildRow capacity (items.get ⟨i, hi⟩) up j hj).ret.2]; omega)) := by
  induction j with
  | zero =>
      intro c hc
      have : c = 0 := by omega
      subst c
      simp only [solve.buildRow, TimeM.ret_bind, TimeM.ret_pure]
      simpa using optimal_step items i 0 hi
        (up.1[0]'(by rw [up.2]; omega)) (up.1[0]'(by rw [up.2]; omega))
        (hu 0 (by omega)) (by simpa using hu 0 (by omega))
  | succ j ih =>
      intro c hc
      simp only [solve.buildRow, TimeM.ret_bind, TimeM.ret_pure]
      rw [Array.getElem_push]
      split
      · rename_i hlt
        exact ih (by omega) c (by
          have hs := (solve.buildRow capacity (items.get ⟨i, hi⟩) up j (by omega)).ret.2
          omega)
      · rename_i hnot
        have hs := (solve.buildRow capacity (items.get ⟨i, hi⟩) up j (by omega)).ret.2
        have hcj : c = j + 1 := by omega
        subst c
        exact optimal_step items i (j + 1) hi
          (up.1[j + 1]'(by rw [up.2]; omega))
          (up.1[j + 1 - (items.get ⟨i, hi⟩).weight]'(by rw [up.2]; omega))
          (hu (j + 1) (by omega)) (hu _ (by omega))

private theorem buildTable_correct (items : List Item) (capacity i : Nat)
    (hi : i ≤ items.toArray.size) :
    ∀ p c (hp : p ≤ i) (hc : c ≤ capacity),
      CellOptimal items p c
        (cell (solve.buildTable capacity items.toArray i hi).ret p c hp hc) := by
  induction i with
  | zero =>
      intro p c hp hc
      have : p = 0 := by omega
      subst p
      simpa [solve.buildTable, cell] using optimal_zero items c
  | succ i ih =>
      intro p c hp hc
      simp only [solve.buildTable, TimeM.ret_bind, TimeM.ret_pure, cell]
      simp only [Array.getElem_push]
      split
      · rename_i hlt
        exact ih (by omega) p c (by
          have hs := (solve.buildTable capacity items.toArray i (by omega)).ret.2.1
          omega) hc
      · rename_i hnot
        have hs := (solve.buildTable capacity items.toArray i (by omega)).ret.2.1
        have hpi : p = i + 1 := by omega
        subst p
        let up : Row capacity :=
          ⟨(solve.buildTable capacity items.toArray i (by omega)).ret.1[i]'(by
            rw [(solve.buildTable capacity items.toArray i (by omega)).ret.2.1]; omega),
            (solve.buildTable capacity items.toArray i (by omega)).ret.2.2 i (by
              rw [(solve.buildTable capacity items.toArray i (by omega)).ret.2.1]; omega)⟩
        have hiItems : i < items.length := by
          simpa using (show i < items.toArray.size from by omega)
        simpa [Array.getElem_toList] using
          buildRow_correct items i hiItems capacity up
            (fun q hq => ih (by omega) i q (by omega) hq)
            capacity (by omega) c hc

private theorem cell_recurrence (items : List Item) (capacity : Nat)
    (table : Table capacity items.toArray.size)
    (ho : ∀ p c (hp : p ≤ items.toArray.size) (hc : c ≤ capacity),
      CellOptimal items p c (cell table p c hp hc))
    (i c : Nat) (hi : i + 1 ≤ items.toArray.size) (hc : c ≤ capacity) :
    cell table (i + 1) c hi hc =
      if (items.get ⟨i, by simpa using (show i < items.toArray.size from by omega)⟩).weight ≤ c
      then max (cell table i c (by omega) hc)
        (cell table i (c - (items.get ⟨i, by
          simpa using (show i < items.toArray.size from by omega)⟩).weight) (by omega) (by omega) +
          (items.get ⟨i, by simpa using (show i < items.toArray.size from by omega)⟩).value)
      else cell table i c (by omega) hc := by
  let idx : Fin items.length := ⟨i, by simpa using (show i < items.toArray.size from by omega)⟩
  change cell table (i + 1) c hi hc =
    if (items.get idx).weight ≤ c then max (cell table i c (by omega) hc)
      (cell table i (c - (items.get idx).weight) (by omega) (by omega) +
        (items.get idx).value)
    else cell table i c (by omega) hc
  exact optimal_unique (ho (i + 1) c hi hc)
    (optimal_step items i c idx.isLt (cell table i c (by omega) hc)
      (cell table i (c - (items.get idx).weight) (by omega) (by omega))
      (ho i c (by omega) hc) (ho i _ (by omega) (by omega)))

private theorem reconstruct_correct (items : List Item) (capacity : Nat)
    (table : Table capacity items.toArray.size)
    (ho : ∀ p c (hp : p ≤ items.toArray.size) (hc : c ≤ capacity),
      CellOptimal items p c (cell table p c hp hc))
    (i c : Nat) (hi : i ≤ items.toArray.size) (hc : c ≤ capacity) :
    let chosen := (solve.reconstruct items capacity cell items.toArray (by simp) table
      i c hi hc).ret
    Within chosen i ∧ Feasible items c chosen ∧
      totalValue items chosen = cell table i c hi hc := by
  induction i generalizing c with
  | zero =>
      simp only [solve.reconstruct, TimeM.ret_pure]
      refine ⟨by simp [Within], by simp [Feasible, totalWeight], ?_⟩
      have hzero := optimal_unique (optimal_zero items c) (ho 0 c hi hc)
      simpa [totalValue] using hzero
  | succ i ih =>
      simp only [solve.reconstruct, TimeM.ret_bind]
      split
      · rename_i heq
        obtain ⟨hwithin, hfeasible, hvalue⟩ := ih c (by omega) hc
        exact ⟨within_mono hwithin (Nat.le_succ i), hfeasible, hvalue.trans heq.symm⟩
      · rename_i hne
        simp only [TimeM.ret_bind, TimeM.ret_pure]
        let idx : Fin items.length :=
          ⟨i, by simpa using (show i < items.toArray.size from by omega)⟩
        have hrec := cell_recurrence items capacity table ho i c hi hc
        change cell table (i + 1) c hi hc ≠ cell table i c (by omega) hc at hne
        change cell table (i + 1) c hi hc =
          if (items.get idx).weight ≤ c then max (cell table i c (by omega) hc)
            (cell table i (c - (items.get idx).weight) (by omega) (by omega) +
              (items.get idx).value)
          else cell table i c (by omega) hc at hrec
        have hfit : (items.get idx).weight ≤ c := by
          by_contra hnot
          simp only [hnot, ↓reduceIte] at hrec
          exact hne hrec
        simp only [hfit, ↓reduceIte] at hrec
        have hbetter : cell table i c (by omega) hc <
            cell table i (c - (items.get idx).weight) (by omega) (by omega) +
              (items.get idx).value := by
          by_contra hnot
          have hmax : max (cell table i c (by omega) hc)
              (cell table i (c - (items.get idx).weight) (by omega) (by omega) +
                (items.get idx).value) = cell table i c (by omega) hc := by
            exact max_eq_left (Nat.le_of_not_gt hnot)
          exact hne (hrec.trans hmax)
        have hcurrent : cell table (i + 1) c hi hc =
            cell table i (c - (items.get idx).weight) (by omega) (by omega) +
              (items.get idx).value := by
          rw [hrec, max_eq_right hbetter.le]
        obtain ⟨hwithin, hfeasible, hvalue⟩ :=
          ih (c - (items.get idx).weight) (by omega) (by omega)
        have hnotmem : idx ∉
            (solve.reconstruct items capacity cell items.toArray (by simp) table i
              (c - (items.get idx).weight) (by omega) (by omega)).ret :=
          not_mem_of_within hwithin idx (by simp [idx])
        let rest := (solve.reconstruct items capacity cell items.toArray (by simp) table i
          (c - (items.get idx).weight) (by omega) (by omega)).ret
        change Within (insert idx rest) (i + 1) ∧
          Feasible items c (insert idx rest) ∧
            totalValue items (insert idx rest) = cell table (i + 1) c hi hc
        constructor
        · exact within_insert hwithin idx (by simp [idx])
        constructor
        · rw [Feasible, totalWeight_insert items _ idx hnotmem]
          rw [Feasible] at hfeasible
          omega
        · rw [totalValue_insert items _ idx hnotmem, hvalue]
          omega

/-- The returned set is feasible, its reported value is its value sum, and it is globally
optimal among all feasible subsets of the input indices. -/
theorem solve_correct (items : List Item) (capacity : Nat) :
    let result := (solve items capacity).ret
    Feasible items capacity result.chosen ∧
      result.value = totalValue items result.chosen ∧
      ∀ chosen : Finset (Fin items.length),
        Feasible items capacity chosen → totalValue items chosen ≤ result.value := by
  let table :=
    (solve.buildTable capacity items.toArray items.toArray.size (by omega)).ret
  have ho := buildTable_correct items capacity items.toArray.size (by omega)
  have hr := reconstruct_correct items capacity table ho items.toArray.size capacity
    (by omega) (by omega)
  have hopt := ho items.toArray.size capacity (by omega) (by omega)
  simp only [solve, TimeM.ret_bind, TimeM.ret_pure]
  change _ ∧ _ ∧ _
  refine ⟨hr.2.1, hr.2.2.symm, ?_⟩
  intro chosen hfeasible
  exact hopt.2 chosen (fun j _ => by simpa only [List.size_toArray] using j.isLt) hfeasible

private theorem buildRow_time (capacity : Nat) (item : Item) (up : Row capacity)
    (c : Nat) (hc : c ≤ capacity) :
    (solve.buildRow capacity item up c hc).time = c + 1 := by
  induction c with
  | zero => simp [solve.buildRow]
  | succ c ih =>
      simp only [solve.buildRow, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
      rw [ih (by omega)]
      omega

private theorem buildTable_time (capacity : Nat) (values : Array Item)
    (i : Nat) (hi : i ≤ values.size) :
    (solve.buildTable capacity values i hi).time = i * (capacity + 1) := by
  induction i with
  | zero => simp [solve.buildTable]
  | succ i ih =>
      simp only [solve.buildTable, TimeM.time_bind, TimeM.time_pure, buildRow_time]
      rw [ih (by omega), Nat.succ_mul]
      omega

private theorem reconstruct_time (items : List Item) (capacity : Nat) (values : Array Item)
    (hvalues : values.size = items.length) (table : Table capacity values.size) (i c : Nat)
    (hi : i ≤ values.size) (hc : c ≤ capacity) :
    (solve.reconstruct items capacity cell values hvalues table i c hi hc).time = i := by
  induction i generalizing c with
  | zero => simp [solve.reconstruct]
  | succ i ih =>
      simp only [solve.reconstruct, TimeM.time_bind, TimeM.time_tick]
      split
      · rw [ih]
        omega
      · simp only [TimeM.time_bind, TimeM.time_pure]
        rw [ih]
        omega

/-- The exact cost is one tick per table cell and one tick per reconstructed item row. -/
theorem solve_time (items : List Item) (capacity : Nat) :
    (solve items capacity).time =
      items.length * (capacity + 1) + items.length := by
  simp only [solve, TimeM.time_bind, TimeM.time_pure, buildTable_time,
    reconstruct_time, List.size_toArray]
  omega

/-- For positive capacity, the exact pseudo-polynomial cost is at most `3 * n * W`. -/
theorem solve_time_le_three_mul (items : List Item) (capacity : Nat)
    (hcapacity : 0 < capacity) :
    (solve items capacity).time ≤ 3 * (items.length * capacity) := by
  rw [solve_time, Nat.mul_add, Nat.mul_one]
  have hcapacity' : 1 ≤ capacity := hcapacity
  have hn := Nat.mul_le_mul_left items.length hcapacity'
  simp only [Nat.mul_one] at hn
  omega

end Cslib.Algorithms.Lean.TimeM.Knapsack
