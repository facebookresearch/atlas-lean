/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Order.Bounds.Basic

import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Bottom-up rod cutting

The rod-cutting dynamic program from CLRS, fourth edition, Section 14.1, pages 363-370.
Prices describe positive integer piece lengths, cuts are free, and every piece of the original
rod must be sold. Mathlib's `Composition` records exactly these valid ordered decompositions.
The extended revenue/first-cut tables and their saved-cut reconstruction follow pages 371-372.
Strict improvement while scanning increasing first cuts selects the least optimal first cut
in each row; this is not a lexicographic claim about the complete emitted decomposition.

The revenue domain admits signed and fractional prices as a documented generalization of the
nonnegative sales interpretation. Each positive row starts with its first real candidate, so
negative revenue does not introduce an option to discard the rod.

The cost model counts one tick per evaluated first-cut candidate. Table allocation, access,
updates, comparisons, addition, and loop control are free. It describes candidate evaluations,
not arithmetic bit complexity or wall time.
Reconstruction adds one tick adjacent to each emitted positive block. These candidate/output
events do not represent the full CLRS RAM-operation cost.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.RodCutting

universe u

open scoped BigOperators

/-- Revenue obtained by selling every positive block of a rod composition.
The price vector's entry `i - 1` is the price of a piece of length `i`. -/
@[expose] public def compositionRevenue {α : Type u} [AddCommMonoid α] {n k : Nat}
    (prices : Vector α n) (parts : Composition k) (hk : k ≤ n) : α :=
  (parts.blocks.pmap
    (fun i (hi : 0 < i ∧ i ≤ n) => prices[i - 1]'(by omega))
    (fun i hi => ⟨parts.blocks_pos hi, (parts.blocks_le hi).trans hk⟩)).sum

/-- The empty rod earns zero revenue. -/
@[simp] public theorem compositionRevenue_zero {α : Type u} [AddCommMonoid α] {n : Nat}
    (prices : Vector α n) (parts : Composition 0) :
    compositionRevenue prices parts (Nat.zero_le n) = 0 := by
  have hempty : parts.blocks = [] := parts.blocks_eq_nil.mpr rfl
  simp [compositionRevenue, hempty]

/-- Selling the rod without a cut earns its supplied price. -/
@[simp] public theorem compositionRevenue_single {α : Type u} [AddCommMonoid α]
    {n k : Nat} (prices : Vector α n) (hk : k ≤ n) (hpos : 0 < k) :
    compositionRevenue prices (Composition.single k hpos) hk =
      prices[k - 1]'(by omega) := by
  simp [compositionRevenue, Composition.single]

/-- Revenue is additive when two whole-rod compositions are concatenated. -/
public theorem compositionRevenue_append {α : Type u} [AddCommMonoid α]
    {n k l : Nat} (prices : Vector α n) (left : Composition k) (right : Composition l)
    (hkl : k + l ≤ n) :
    compositionRevenue prices (left.append right) hkl =
      compositionRevenue prices left (by omega) +
      compositionRevenue prices right (by omega) := by
  simp [compositionRevenue, Composition.append, List.pmap_append]

@[no_expose] private def candidate {α : Type u} [Add α] {n : Nat}
    (prices : Vector α n) (table : Vector α (n + 1)) (j : Nat) (hjn : j ≤ n)
    (i : Fin j) : α :=
  prices[i.val]'(by omega) + table[j - (i.val + 1)]'(by omega)

@[no_expose] private def scanCuts {α : Type u} [Add α] [LinearOrder α] {n : Nat}
    (prices : Vector α n) (table : Vector α (n + 1)) (j : Nat) (hjn : j ≤ n) :
    (count : Nat) → count < j → TimeM Nat α
  | 0, hcount => do
      TimeM.tick 1
      pure (candidate prices table j hjn ⟨0, hcount⟩)
  | count + 1, hcount => do
      let best ← scanCuts prices table j hjn count (by omega)
      TimeM.tick 1
      pure (max best (candidate prices table j hjn ⟨count + 1, hcount⟩))

@[no_expose] private def fillRows {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) :
    (count : Nat) → count ≤ n → TimeM Nat (Vector α (n + 1))
  | 0, _ => pure (Vector.replicate (n + 1) 0)
  | count + 1, hcount => do
      let table ← fillRows prices count (by omega)
      let best ← scanCuts prices table (count + 1) hcount count (by omega)
      pure (table.set (count + 1) best)

/-- Compute the maximum revenue by saving solutions for lengths `0, ..., n` in increasing order.
One cost tick is charged for each evaluated positive first-piece length. -/
public def bottomUpCutRod {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) : TimeM Nat α := do
  let table ← fillRows prices n le_rfl
  pure (table.get (Fin.last n))

private theorem scanCuts_spec {α : Type u} [Add α] [LinearOrder α] {n : Nat}
    (prices : Vector α n) (table : Vector α (n + 1)) (j : Nat) (hjn : j ≤ n)
    (count : Nat) (hcount : count < j) :
    (∃ i : Fin j, i.val ≤ count ∧
      candidate prices table j hjn i = (scanCuts prices table j hjn count hcount).ret) ∧
    ∀ i : Fin j, i.val ≤ count →
      candidate prices table j hjn i ≤ (scanCuts prices table j hjn count hcount).ret := by
  induction count with
  | zero =>
      simp only [scanCuts]
      refine ⟨⟨⟨0, hcount⟩, le_rfl, rfl⟩, ?_⟩
      intro i hi
      have heq : i = ⟨0, hcount⟩ := Fin.ext (by simpa using hi)
      simp [heq]
  | succ count ih =>
      rcases ih (by omega) with ⟨⟨i, hi, heq⟩, hupper⟩
      simp only [scanCuts, TimeM.ret_bind, TimeM.ret_pure]
      refine ⟨?_, ?_⟩
      · by_cases h : candidate prices table j hjn ⟨count + 1, hcount⟩ ≤
            (scanCuts prices table j hjn count (by omega)).ret
        · exact ⟨i, by omega, heq.trans (max_eq_left h).symm⟩
        · exact ⟨⟨count + 1, hcount⟩, le_rfl, (max_eq_right (le_of_not_ge h)).symm⟩
      · intro i hi
        by_cases h : i.val ≤ count
        · exact (hupper i h).trans (le_max_left _ _)
        · have heq : i = ⟨count + 1, hcount⟩ := Fin.ext (show i.val = count + 1 by omega)
          simpa only [heq] using
            (le_max_right (scanCuts prices table j hjn count (by omega)).ret
              (candidate prices table j hjn ⟨count + 1, hcount⟩))

private theorem scanCuts_time {α : Type u} [Add α] [LinearOrder α] {n : Nat}
    (prices : Vector α n) (table : Vector α (n + 1)) (j : Nat) (hjn : j ≤ n)
    (count : Nat) (hcount : count < j) :
    (scanCuts prices table j hjn count hcount).time = count + 1 := by
  induction count with
  | zero => simp [scanCuts]
  | succ count ih => simp [scanCuts, ih (by omega)]

private theorem compositionRevenue_cast {α : Type u} [AddCommMonoid α]
    {n k l : Nat} (prices : Vector α n) (parts : Composition k) (hkl : k = l)
    (hl : l ≤ n) :
    compositionRevenue prices (parts.cast hkl) hl =
      compositionRevenue prices parts (by omega) := by
  subst l
  rfl

@[no_expose] private def TableOptimal {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (table : Vector α (n + 1)) (count : Nat) : Prop :=
  ∀ (k : Nat) (hk : k ≤ n), k ≤ count →
    IsGreatest (Set.range fun parts : Composition k => compositionRevenue prices parts hk)
      table[k]

private theorem row_optimal {α : Type u} [AddCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n) (table : Vector α (n + 1))
    (j : Nat) (hjn : j ≤ n) (hpos : 0 < j) (hoptimal : TableOptimal prices table (j - 1)) :
    IsGreatest (Set.range fun parts : Composition j => compositionRevenue prices parts hjn)
      (scanCuts prices table j hjn (j - 1) (by omega)).ret := by
  obtain ⟨⟨i, _, hbest⟩, hupper⟩ := scanCuts_spec prices table j hjn (j - 1) (by omega)
  constructor
  · obtain ⟨parts, hparts⟩ := (hoptimal (j - (i.val + 1)) (by omega) (by omega)).1
    refine ⟨((Composition.single (i.val + 1) (by omega)).append parts).cast
      (by omega), ?_⟩
    dsimp only at hparts ⊢
    rw [compositionRevenue_cast, compositionRevenue_append, compositionRevenue_single,
      hparts]
    simpa only [candidate, Nat.add_sub_cancel] using hbest
  · rintro revenue ⟨parts, rfl⟩
    induction parts using Composition.recOnSingleAppend with
    | zero => omega
    | single_append k m parts _ih =>
        have hm : m ≤ n := by omega
        have hsaved := (hoptimal m hm (by omega)).2
          (Set.mem_range_self parts)
        have hcut := hupper ⟨k, by omega⟩ (by omega)
        dsimp only
        rw [compositionRevenue_append, compositionRevenue_single]
        refine (add_le_add_right hsaved _).trans ?_
        simpa only [candidate, Nat.add_sub_cancel, Nat.add_sub_cancel_left] using hcut

private theorem fillRows_optimal {α : Type u} [AddCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n) (count : Nat)
    (hcount : count ≤ n) : TableOptimal prices (fillRows prices count hcount).ret count := by
  induction count with
  | zero =>
      intro k hk hzero
      have heq : k = 0 := by omega
      subst k
      simp only [fillRows, TimeM.ret_pure, Vector.getElem_replicate]
      constructor
      · exact ⟨Composition.ones 0, compositionRevenue_zero prices _⟩
      · rintro revenue ⟨parts, rfl⟩
        simp
  | succ count ih =>
      have hprevious := ih (by omega)
      have hrow := row_optimal prices (fillRows prices count (by omega)).ret
        (count + 1) hcount (by omega) (by simpa using hprevious)
      intro k hk hcompleted
      simp only [fillRows, TimeM.ret_bind, TimeM.ret_pure]
      by_cases hnew : k = count + 1
      · subst k
        simpa only [Vector.getElem_set_self, Nat.add_sub_cancel] using hrow
      · rw [Vector.getElem_set_ne (by omega) (by omega) (by omega)]
        exact hprevious k hk (by omega)

private theorem fillRows_time {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (count : Nat) (hcount : count ≤ n) :
    (fillRows prices count hcount).time = ∑ j ∈ Finset.range (count + 1), j := by
  induction count with
  | zero => simp [fillRows]
  | succ count ih =>
      simp [fillRows, ih (by omega), scanCuts_time, Finset.sum_range_succ]

@[expose] public section

/-- The computed revenue is attained by a whole-rod composition and dominates every such revenue.
This covers signed prices without offering an option to discard any material. -/
theorem bottomUpCutRod_correct {α : Type u} [AddCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n) :
    IsGreatest (Set.range fun parts : Composition n => compositionRevenue prices parts le_rfl)
      (bottomUpCutRod prices).ret := by
  simpa only [bottomUpCutRod, TimeM.ret_bind, TimeM.ret_pure, Vector.get_eq_getElem,
    Fin.val_last] using fillRows_optimal prices n le_rfl n le_rfl le_rfl

/-- Empty input needs no candidate evaluation and earns zero. -/
@[simp] theorem bottomUpCutRod_zero {α : Type u} [AddCommMonoid α] [LinearOrder α]
    (prices : Vector α 0) : bottomUpCutRod prices = pure 0 := by
  simp [bottomUpCutRod, fillRows, Vector.get_eq_getElem]

/-- The executable evaluates exactly `j` candidates in row `j`. -/
theorem bottomUpCutRod_time_sum {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) :
    (bottomUpCutRod prices).time = ∑ j ∈ Finset.range (n + 1), j := by
  simpa [bottomUpCutRod] using fillRows_time prices n le_rfl

/-- Twice the actual candidate count is `n * (n + 1)`. -/
theorem bottomUpCutRod_time_twice {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) :
    2 * (bottomUpCutRod prices).time = n * (n + 1) := by
  rw [bottomUpCutRod_time_sum, Nat.mul_comm 2,
    Finset.sum_range_id_mul_two, Nat.add_sub_cancel, Nat.mul_comm]

/-- The actual candidate count is the triangular number, independent of all prices. -/
theorem bottomUpCutRod_time {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) :
    (bottomUpCutRod prices).time = n * (n + 1) / 2 := by
  rw [bottomUpCutRod_time_sum, Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]

/-- Matching quadratic bounds in the stated candidate-evaluation cost model. -/
theorem bottomUpCutRod_time_bounds {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) :
    n ^ 2 ≤ 2 * (bottomUpCutRod prices).time ∧ (bottomUpCutRod prices).time ≤ n ^ 2 := by
  constructor
  · rw [bottomUpCutRod_time_twice, pow_two]
    exact Nat.mul_le_mul_left n (by omega)
  · rw [bottomUpCutRod_time_sum, Finset.sum_range_succ']
    simp only [Nat.add_zero, pow_two]
    calc
      ∑ j ∈ Finset.range n, (j + 1) ≤ ∑ _j ∈ Finset.range n, n :=
        Finset.sum_le_sum fun j hj => by
          have h := Finset.mem_range.mp hj
          omega
      _ = n * n := by simp

end

/-! ### Saved first cuts -/

@[no_expose] private def scanCutsWithIndex {α : Type u} [Add α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (table : Vector α (n + 1)) (j : Nat)
    (hjn : j ≤ n) : (count : Nat) → count < j → TimeM Nat (α × Fin j)
  | 0, hcount => do
      TimeM.tick 1
      pure (candidate prices table j hjn ⟨0, hcount⟩, ⟨0, hcount⟩)
  | count + 1, hcount => do
      let best ← scanCutsWithIndex prices table j hjn count (by omega)
      TimeM.tick 1
      let next := candidate prices table j hjn ⟨count + 1, hcount⟩
      pure (if best.1 < next then (next, ⟨count + 1, hcount⟩) else best)

private lemma scanCutsWithIndex_ret {α : Type u} [Add α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (table : Vector α (n + 1)) (j : Nat)
    (hjn : j ≤ n) (count : Nat) (hcount : count < j) :
    (scanCutsWithIndex prices table j hjn count hcount).ret.1 =
      (scanCuts prices table j hjn count hcount).ret := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [scanCutsWithIndex, scanCuts, TimeM.ret_bind, TimeM.ret_pure]
      rw [← ih (by omega)]
      split
      · exact (max_eq_right (le_of_lt ‹_›)).symm
      · exact (max_eq_left (le_of_not_gt ‹_›)).symm

private lemma scanCutsWithIndex_time {α : Type u} [Add α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (table : Vector α (n + 1)) (j : Nat)
    (hjn : j ≤ n) (count : Nat) (hcount : count < j) :
    (scanCutsWithIndex prices table j hjn count hcount).time = count + 1 := by
  induction count with
  | zero => simp [scanCutsWithIndex]
  | succ count ih => simp [scanCutsWithIndex, ih (by omega)]

private lemma scanCutsWithIndex_attained {α : Type u} [Add α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (table : Vector α (n + 1)) (j : Nat)
    (hjn : j ≤ n) (count : Nat) (hcount : count < j) :
    (scanCutsWithIndex prices table j hjn count hcount).ret.2.val ≤ count ∧
      candidate prices table j hjn
        (scanCutsWithIndex prices table j hjn count hcount).ret.2 =
        (scanCutsWithIndex prices table j hjn count hcount).ret.1 := by
  induction count with
  | zero => exact ⟨le_rfl, rfl⟩
  | succ count ih =>
      obtain ⟨hindex, hattain⟩ := ih (by omega)
      simp only [scanCutsWithIndex, TimeM.ret_bind, TimeM.ret_pure]
      split
      · exact ⟨le_rfl, rfl⟩
      · exact ⟨by omega, hattain⟩

private lemma scanCutsWithIndex_first {α : Type u} [Add α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (table : Vector α (n + 1)) (j : Nat)
    (hjn : j ≤ n) (count : Nat) (hcount : count < j) (i : Fin j)
    (hi : i.val < (scanCutsWithIndex prices table j hjn count hcount).ret.2.val) :
    candidate prices table j hjn i <
      (scanCutsWithIndex prices table j hjn count hcount).ret.1 := by
  induction count generalizing i with
  | zero =>
      simp only [scanCutsWithIndex, TimeM.ret_bind, TimeM.ret_pure] at hi
      omega
  | succ count ih =>
      simp only [scanCutsWithIndex, TimeM.ret_bind, TimeM.ret_pure] at hi ⊢
      by_cases h : (scanCutsWithIndex prices table j hjn count (by omega)).ret.1 <
          candidate prices table j hjn ⟨count + 1, hcount⟩
      · simp only [ite_eq_left h] at hi ⊢
        have hupper := (scanCuts_spec prices table j hjn count (by omega)).2 i
          (by omega)
        rw [← scanCutsWithIndex_ret] at hupper
        exact hupper.trans_lt h
      · simp only [ite_eq_right h] at hi ⊢
        exact ih (by omega) i hi

@[no_expose] private def fillRowsWithCuts {α : Type u} [AddCommMonoid α]
    [LinearOrder α] {n : Nat} (prices : Vector α n) :
    (count : Nat) → count ≤ n → TimeM Nat (Vector α (n + 1) × Vector Nat n)
  | 0, _ => pure (Vector.replicate (n + 1) 0, Vector.replicate n 0)
  | count + 1, hcount => do
      let tables ← fillRowsWithCuts prices count (by omega)
      let best ← scanCutsWithIndex prices tables.1 (count + 1) hcount count (by omega)
      pure (tables.1.set (count + 1) best.1, tables.2.set count (best.2.val + 1))

private lemma fillRowsWithCuts_ret {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (count : Nat) (hcount : count ≤ n) :
    (fillRowsWithCuts prices count hcount).ret.1 = (fillRows prices count hcount).ret := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [fillRowsWithCuts, fillRows, TimeM.ret_bind, TimeM.ret_pure,
        scanCutsWithIndex_ret, ih (by omega)]

private lemma fillRowsWithCuts_time {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (count : Nat) (hcount : count ≤ n) :
    (fillRowsWithCuts prices count hcount).time = (fillRows prices count hcount).time := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [fillRowsWithCuts, fillRows, ih (by omega), scanCutsWithIndex_time,
        scanCuts_time]

/-- Save all optimal revenues and the first maximizing cut at each positive length.
The source's `r[j]` is the revenue vector's entry `j`; `s[j]` is the cut vector's
entry `j - 1`. Ascending candidates update only on strict improvement.
One event is charged per candidate, including the first candidate of each row. -/
public def extendedBottomUpCutRod {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) : TimeM Nat (Vector α (n + 1) × Vector Nat n) :=
  fillRowsWithCuts prices n le_rfl

/-- Every saved revenue is attained by a whole-rod composition and dominates all its competitors. -/
public theorem extendedBottomUpCutRod_correct {α : Type u} [AddCommMonoid α]
    [LinearOrder α] [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n)
    (j : Nat) (hjn : j ≤ n) :
    IsGreatest (Set.range fun parts : Composition j => compositionRevenue prices parts hjn)
      (extendedBottomUpCutRod prices).ret.1[j] := by
  change IsGreatest _ (fillRowsWithCuts prices n le_rfl).ret.1[j]
  rw [fillRowsWithCuts_ret]
  exact fillRows_optimal prices n le_rfl j hjn hjn

/-- The final saved revenue is exactly the existing bottom-up solver's result. -/
public theorem extendedBottomUpCutRod_revenue_eq {α : Type u} [AddCommMonoid α]
    [LinearOrder α] {n : Nat} (prices : Vector α n) :
    (extendedBottomUpCutRod prices).ret.1[n] = (bottomUpCutRod prices).ret := by
  simp only [extendedBottomUpCutRod, fillRowsWithCuts_ret, bottomUpCutRod,
    TimeM.ret_bind, TimeM.ret_pure, Vector.get_eq_getElem, Fin.val_last]

/-- The saved tables execute exactly the triangular number of candidate events. -/
public theorem extendedBottomUpCutRod_time {α : Type u} [AddCommMonoid α]
    [LinearOrder α] {n : Nat} (prices : Vector α n) :
    (extendedBottomUpCutRod prices).time = n * (n + 1) / 2 := by
  change (fillRowsWithCuts prices n le_rfl).time = _
  rw [fillRowsWithCuts_time]
  simpa [bottomUpCutRod] using bottomUpCutRod_time prices

/-- Empty input returns its zero revenue row, no cut entries and no candidate events. -/
@[simp] public theorem extendedBottomUpCutRod_zero {α : Type u} [AddCommMonoid α]
    [LinearOrder α] (prices : Vector α 0) :
    extendedBottomUpCutRod prices = pure (Vector.replicate 1 0, Vector.replicate 0 0) := by
  simp [extendedBottomUpCutRod, fillRowsWithCuts]

private lemma candidate_set {α : Type u} [Add α] {n : Nat}
    (prices : Vector α n) (table : Vector α (n + 1)) (k : Nat)
    (hk : k < n + 1) (value : α) (j : Nat) (hjn : j ≤ n)
    (hjk : j ≤ k) (i : Fin j) :
    candidate prices (table.set k value hk) j hjn i =
      candidate prices table j hjn i := by
  simp only [candidate]
  rw [Vector.getElem_set_ne (i := k) (j := j - (i.val + 1)) hk (by omega) (by omega)]

@[no_expose] private def FirstCutsValid {α : Type u} [Add α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (table : Vector α (n + 1))
    (cuts : Vector Nat n) (count : Nat) : Prop :=
  ∀ (j : Nat) (hjn : j ≤ n) (hpos : 0 < j), j ≤ count →
    ∃ i : Fin j, cuts[j - 1]'(by omega) = i.val + 1 ∧
      candidate prices table j hjn i = table[j] ∧
      ∀ h : Fin j, h.val < i.val → candidate prices table j hjn h < table[j]

private lemma firstCutsValid_set {α : Type u} [Add α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (table : Vector α (n + 1))
    (cuts : Vector Nat n) (count k : Nat) (hkn : k ≤ n) (hcount : count < k)
    (value : α) (cut : Nat) (hvalid : FirstCutsValid prices table cuts count) :
    FirstCutsValid prices (table.set k value (by omega))
      (cuts.set (k - 1) cut (by omega)) count := by
  intro j hjn hpos hjcount
  obtain ⟨i, hcut, hattain, hfirst⟩ := hvalid j hjn hpos hjcount
  refine ⟨i, ?_, ?_, ?_⟩
  · rw [Vector.getElem_set_ne (i := k - 1) (j := j - 1) (by omega)
      (by omega) (by omega)]
    exact hcut
  · rw [candidate_set prices table k (by omega) value j hjn (by omega),
      Vector.getElem_set_ne (i := k) (j := j) (by omega) (by omega) (by omega)]
    exact hattain
  · intro h hh
    rw [candidate_set prices table k (by omega) value j hjn (by omega),
      Vector.getElem_set_ne (i := k) (j := j) (by omega) (by omega) (by omega)]
    exact hfirst h hh

private lemma fillRowsWithCuts_first {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (count : Nat) (hcount : count ≤ n) :
    FirstCutsValid prices (fillRowsWithCuts prices count hcount).ret.1
      (fillRowsWithCuts prices count hcount).ret.2 count := by
  induction count with
  | zero => intro j hjn hpos hjcount; omega
  | succ count ih =>
      let previous := (fillRowsWithCuts prices count (by omega)).ret
      let best := (scanCutsWithIndex prices previous.1 (count + 1) hcount count
        (by omega)).ret
      have hprevious : FirstCutsValid prices previous.1 previous.2 count := ih (by omega)
      have hsave := firstCutsValid_set prices previous.1 previous.2 count (count + 1)
        hcount (by omega) best.1 (best.2.val + 1) hprevious
      change FirstCutsValid prices (previous.1.set (count + 1) best.1)
        (previous.2.set count (best.2.val + 1)) (count + 1)
      intro j hjn hpos hjcount
      by_cases hnew : j = count + 1
      · subst j
        refine ⟨best.2, ?_, ?_, ?_⟩
        · simp only [Nat.add_sub_cancel, Vector.getElem_set_self]
        · rw [candidate_set prices previous.1 (count + 1) (by omega) best.1
            (count + 1) hjn le_rfl, Vector.getElem_set_self]
          exact (scanCutsWithIndex_attained prices previous.1 (count + 1) hcount
            count (by omega)).2
        · intro h hh
          rw [candidate_set prices previous.1 (count + 1) (by omega) best.1
            (count + 1) hjn le_rfl, Vector.getElem_set_self]
          exact scanCutsWithIndex_first prices previous.1 (count + 1) hcount count
            (by omega) h hh
      · exact hsave j hjn hpos (by omega)

/-- The actual saved positive cut attains the row revenue, and every smaller first cut loses.
The witness `i : Fin j` represents the positive piece length `i.val + 1`. -/
public theorem extendedBottomUpCutRod_firstCut {α : Type u} [AddCommMonoid α]
    [LinearOrder α] {n : Nat} (prices : Vector α n) (j : Nat) (hpos : 0 < j)
    (hjn : j ≤ n) :
    ∃ i : Fin j, (extendedBottomUpCutRod prices).ret.2[j - 1]'(by omega) = i.val + 1 ∧
      prices[i.val]'(by omega) +
        (extendedBottomUpCutRod prices).ret.1[j - (i.val + 1)]'(by omega) =
        (extendedBottomUpCutRod prices).ret.1[j] ∧
      ∀ h : Fin j, h.val < i.val →
        prices[h.val]'(by omega) +
          (extendedBottomUpCutRod prices).ret.1[j - (h.val + 1)]'(by omega) <
          (extendedBottomUpCutRod prices).ret.1[j] := by
  simpa only [extendedBottomUpCutRod, candidate] using
    (fillRowsWithCuts_first prices n le_rfl) j hjn hpos hjn

@[no_expose] private def CutsBounded {n : Nat} (cuts : Vector Nat n) : Prop :=
  ∀ (j : Nat) (hpos : 0 < j) (hjn : j ≤ n),
    0 < cuts[j - 1]'(by omega) ∧ cuts[j - 1]'(by omega) ≤ j

private lemma extendedBottomUpCutRod_bounded {α : Type u} [AddCommMonoid α]
    [LinearOrder α] {n : Nat} (prices : Vector α n) :
    CutsBounded (extendedBottomUpCutRod prices).ret.2 := by
  intro j hpos hjn
  obtain ⟨i, hcut, _, _⟩ := extendedBottomUpCutRod_firstCut prices j hpos hjn
  rw [hcut]
  constructor <;> omega

/-! ### Following the saved first cuts -/

@[no_expose] private def reconstructCuts {n : Nat} (cuts : Vector Nat n)
    (hbounded : CutsBounded cuts) :
    (remaining : Nat) → remaining ≤ n → TimeM Nat (Composition remaining)
  | 0, _ => pure (Composition.ones 0)
  | remaining + 1, hremaining => do
      let cut := cuts[remaining]'(by omega)
      have hcut : 0 < cut ∧ cut ≤ remaining + 1 :=
        hbounded (remaining + 1) (by omega) hremaining
      TimeM.tick 1
      let parts ← reconstructCuts cuts hbounded (remaining + 1 - cut) (by omega)
      pure (((Composition.single cut hcut.1).append parts).cast (by omega))
termination_by remaining _ => remaining
decreasing_by omega

/-- Compute the saved tables once, then emit each successive saved first cut in source order.
The returned composition sells the whole rod. In addition to candidate events,
one event is charged per emitted positive piece; allocation and arithmetic remain free. -/
public def cutRodSolution {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) : TimeM Nat (Composition n) :=
  let tables := extendedBottomUpCutRod prices
  TimeM.bind tables fun _ =>
    reconstructCuts tables.ret.2 (extendedBottomUpCutRod_bounded prices) n le_rfl

private lemma reconstructCuts_time {n : Nat} (cuts : Vector Nat n)
    (hbounded : CutsBounded cuts) (remaining : Nat) (hremaining : remaining ≤ n) :
    (reconstructCuts cuts hbounded remaining hremaining).time =
      (reconstructCuts cuts hbounded remaining hremaining).ret.length := by
  revert hremaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      intro hremaining
      cases remaining with
      | zero => simp [reconstructCuts, Composition.length, Composition.ones]
      | succ remaining =>
          have hcut : 0 < cuts[remaining]'(by omega) ∧ cuts[remaining]'(by omega) ≤
              remaining + 1 := by
            simpa only [Nat.add_sub_cancel] using
              hbounded (remaining + 1) (by omega) hremaining
          have htail := ih (remaining + 1 - cuts[remaining]'(by omega))
            (by omega) (by omega)
          simp [reconstructCuts, Composition.length, Composition.cast,
            Composition.append, Composition.single, htail, Nat.add_comm]

/-- The actual cost is candidate events plus one event for every emitted piece. -/
public theorem cutRodSolution_time {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) :
    (cutRodSolution prices).time = n * (n + 1) / 2 + (cutRodSolution prices).ret.length := by
  simp only [cutRodSolution, TimeM.bind]
  rw [reconstructCuts_time, extendedBottomUpCutRod_time]

private lemma reconstructCuts_blocks {n : Nat} (cuts : Vector Nat n)
    (hbounded : CutsBounded cuts) (remaining : Nat) (hremaining : remaining ≤ n)
    (i : Nat) (hi : i < (reconstructCuts cuts hbounded remaining hremaining).ret.length) :
    cuts[remaining - (reconstructCuts cuts hbounded remaining hremaining).ret.sizeUpTo i - 1]? =
      some ((reconstructCuts cuts hbounded remaining hremaining).ret.blocks[i]'hi) := by
  revert hremaining i
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      intro hremaining i hi
      cases remaining with
      | zero => simp [reconstructCuts, Composition.length, Composition.ones] at hi
      | succ remaining =>
          have hcut : 0 < cuts[remaining]'(by omega) ∧ cuts[remaining]'(by omega) ≤
              remaining + 1 := by
            simpa only [Nat.add_sub_cancel] using
              hbounded (remaining + 1) (by omega) hremaining
          cases i with
          | zero =>
              simp [reconstructCuts, Composition.cast, Composition.append,
                Composition.single, Composition.sizeUpTo]
          | succ i =>
              have hi' : i < (reconstructCuts cuts hbounded
                  (remaining + 1 - cuts[remaining]'(by omega)) (by omega)).ret.length := by
                simpa [reconstructCuts, Composition.length, Composition.cast,
                  Composition.append, Composition.single] using hi
              have htail := ih (remaining + 1 - cuts[remaining]'(by omega))
                (by omega) (by omega) i hi'
              simpa [reconstructCuts, Composition.cast, Composition.append,
                Composition.single, Composition.sizeUpTo, List.take_succ_cons,
                Nat.sub_add_eq] using htail

/-- Each emitted block is the actual saved first cut for the remainder after earlier blocks.
The successful optional lookup also witnesses that this saved entry is in bounds. -/
public theorem cutRodSolution_blocks {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (i : Nat)
    (hi : i < (cutRodSolution prices).ret.length) :
    (extendedBottomUpCutRod prices).ret.2[n - (cutRodSolution prices).ret.sizeUpTo i - 1]? =
      some ((cutRodSolution prices).ret.blocks[i]'hi) := by
  change (extendedBottomUpCutRod prices).ret.2[
    n - (reconstructCuts (extendedBottomUpCutRod prices).ret.2
      (extendedBottomUpCutRod_bounded prices) n le_rfl).ret.sizeUpTo i - 1]? = _
  exact reconstructCuts_blocks (extendedBottomUpCutRod prices).ret.2
    (extendedBottomUpCutRod_bounded prices) n le_rfl i hi

private lemma fillRows_zero {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (count : Nat) (hcount : count ≤ n) :
    (fillRows prices count hcount).ret[0] = 0 := by
  induction count with
  | zero => simp [fillRows]
  | succ count ih =>
      simp only [fillRows, TimeM.ret_bind, TimeM.ret_pure]
      rw [Vector.getElem_set_ne (i := count + 1) (j := 0) (by omega)
        (by omega) (by omega)]
      exact ih (by omega)

private lemma reconstructCuts_revenue {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) (table : Vector α (n + 1)) (cuts : Vector Nat n)
    (hbounded : CutsBounded cuts) (hfirst : FirstCutsValid prices table cuts n)
    (hzero : table[0] = 0) (remaining : Nat) (hremaining : remaining ≤ n) :
    compositionRevenue prices (reconstructCuts cuts hbounded remaining hremaining).ret
      hremaining = table[remaining] := by
  revert hremaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      intro hremaining
      cases remaining with
      | zero => simp [reconstructCuts, compositionRevenue_zero, hzero]
      | succ remaining =>
          have hcut : 0 < cuts[remaining]'(by omega) ∧ cuts[remaining]'(by omega) ≤
              remaining + 1 := by
            simpa only [Nat.add_sub_cancel] using
              hbounded (remaining + 1) (by omega) hremaining
          obtain ⟨i, hchosen, hattain, _⟩ :=
            hfirst (remaining + 1) hremaining (by omega) hremaining
          simp only [Nat.add_sub_cancel] at hchosen
          have htail := ih (remaining + 1 - cuts[remaining]'(by omega))
            (by omega) (by omega)
          simp only [reconstructCuts, TimeM.ret_bind, TimeM.ret_pure]
          rw [compositionRevenue_cast, compositionRevenue_append,
            compositionRevenue_single, htail]
          simpa only [candidate, hchosen, Nat.add_sub_cancel] using hattain

/-- Following tight saved cuts earns exactly the final saved revenue. -/
public theorem cutRodSolution_revenue {α : Type u} [AddCommMonoid α] [LinearOrder α]
    {n : Nat} (prices : Vector α n) :
    compositionRevenue prices (cutRodSolution prices).ret le_rfl =
      (extendedBottomUpCutRod prices).ret.1[n] := by
  have hzero : (extendedBottomUpCutRod prices).ret.1[0] = 0 := by
    simp only [extendedBottomUpCutRod, fillRowsWithCuts_ret]
    exact fillRows_zero prices n le_rfl
  simpa only [cutRodSolution, TimeM.bind] using reconstructCuts_revenue prices
    (extendedBottomUpCutRod prices).ret.1 (extendedBottomUpCutRod prices).ret.2
    (extendedBottomUpCutRod_bounded prices) (fillRowsWithCuts_first prices n le_rfl)
    hzero n le_rfl

/-- The reconstructed whole-rod composition earns a greatest possible canonical revenue. -/
public theorem cutRodSolution_correct {α : Type u} [AddCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] {n : Nat} (prices : Vector α n) :
    IsGreatest (Set.range fun parts : Composition n => compositionRevenue prices parts le_rfl)
      (compositionRevenue prices (cutRodSolution prices).ret le_rfl) := by
  rw [cutRodSolution_revenue]
  exact extendedBottomUpCutRod_correct prices n le_rfl

/-- The empty rod returns the empty canonical composition and charges no events. -/
public theorem cutRodSolution_zero {α : Type u} [AddCommMonoid α] [LinearOrder α] :
    cutRodSolution (#v[] : Vector α 0) = pure (Composition.ones 0) := by
  apply TimeM.ext <;>
    simp [cutRodSolution, extendedBottomUpCutRod, fillRowsWithCuts, reconstructCuts, TimeM.bind]

end Cslib.Algorithms.Lean.RodCutting
