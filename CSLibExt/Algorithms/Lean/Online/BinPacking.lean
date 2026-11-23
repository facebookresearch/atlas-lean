/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Real.Basic

import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Next Fit bin packing

Next Fit (close the current bin when the next item does not fit)
uses at most twice as many unit bins as any feasible packing: the
loads of consecutive Next Fit bins sum to more than `1`, while any
feasible packing bounds the total size by its bin count. This file
covers the Next Fit half of roadmap package ALG-42b of the Atlas
TCS canon roadmap.

Source: D. S. Johnson, Near-Optimal Bin Packing Algorithms (1973).
-/

namespace Cslib.Algorithms.Lean.Online.BinPacking

open Finset

/-- Next Fit bin packing with unit bins: scan the items keeping the
current bin's load; when the next item does not fit, close the bin
and start a new one. `nextFitAux items bins load` processes `items`
given `bins` bins already started and current load `load`. -/
noncomputable def nextFitAux : List ℝ → ℕ → ℝ → ℕ
  | [], bins, _ => bins
  | x :: xs, bins, load => if load + x ≤ 1 then nextFitAux xs bins (load + x)
      else nextFitAux xs (bins + 1) x

/-- The number of bins Next Fit uses on a list of item sizes. -/
noncomputable def nextFitBins : List ℝ → ℕ
  | [] => 0
  | x :: xs => nextFitAux xs 1 x

/-- An assignment of item indices to bins is feasible for `B` bins if
all item sizes lie in `[0, 1]`, every item is assigned to a bin below `B`,
and every bin's total size is at most `1`. Zero-size items are allowed.
Coverage is part of the definition: without it an assignment could send items to bins
outside the range, and the per-bin bound alone would hold vacuously. -/
def FeasibleAssignment (sizes : List ℝ) (B : ℕ) (a : ℕ → ℕ) : Prop :=
  (∀ x ∈ sizes, 0 ≤ x ∧ x ≤ 1) ∧
  (∀ i, i < sizes.length → a i < B) ∧
  ∀ b, b < B → (∑ i ∈ (Finset.range sizes.length).filter (fun i => a i = b),
    sizes.getD i 0) ≤ 1

private noncomputable def nextFitAuxLoad : List ℝ → ℝ → ℝ
  | [], load => load
  | x :: xs, load => if load + x ≤ 1 then nextFitAuxLoad xs (load + x)
      else nextFitAuxLoad xs x

private theorem nextFitAux_bound (items : List ℝ) (bins : ℕ) (load : ℝ)
    (hnonneg : ∀ x ∈ items, 0 ≤ x) :
    (nextFitAux items bins load : ℝ) + nextFitAuxLoad items load
      ≤ bins + load + 2 * items.sum := by
  induction items generalizing bins load with
  | nil =>
    simp only [nextFitAux.eq_1, nextFitAuxLoad.eq_1, List.sum_nil, mul_zero,
      add_zero, le_refl]
  | cons x xs ih =>
    have hxs : ∀ y ∈ xs, 0 ≤ y := fun y hy => hnonneg y (List.mem_cons_of_mem x hy)
    have hx : 0 ≤ x := hnonneg x List.mem_cons_self
    by_cases h : load + x ≤ 1
    · simp only [nextFitAux.eq_2, nextFitAuxLoad.eq_2, h, ↓reduceIte]
      have hi := ih bins (load + x) hxs
      simp only [List.sum_cons] at hi ⊢
      linarith
    · simp only [nextFitAux.eq_2, nextFitAuxLoad.eq_2, h, ↓reduceIte]
      have hi := ih (bins + 1) x hxs
      simp only [List.sum_cons] at hi ⊢
      push_cast at hi ⊢
      have hlt : (1 : ℝ) < load + x := lt_of_not_ge h
      linarith

private theorem nextFitAuxLoad_pos (items : List ℝ) (load : ℝ)
    (hitems : ∀ x ∈ items, 0 ≤ x ∧ x ≤ 1) (hload0 : 0 < load) (hload1 : load ≤ 1) :
    0 < nextFitAuxLoad items load := by
  induction items generalizing load with
  | nil => simpa [nextFitAuxLoad.eq_1]
  | cons x xs ih =>
    have hxs : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ 1 :=
      fun y hy => hitems y (List.mem_cons_of_mem x hy)
    have hx := hitems x List.mem_cons_self
    by_cases h : load + x ≤ 1
    · simp only [nextFitAuxLoad.eq_2, h, ↓reduceIte]
      exact ih (load + x) hxs (by linarith) h
    · simp only [nextFitAuxLoad.eq_2, h, ↓reduceIte]
      exact ih x hxs (by linarith) hx.2

/-- Either Next Fit never opens a new bin, or its final load is positive: a new
bin starts only with an item that overflows a load of at most `1`, so that item
is positive. -/
private theorem nextFitAux_eq_or_load_pos (items : List ℝ) (bins : ℕ) (load : ℝ)
    (hitems : ∀ x ∈ items, 0 ≤ x ∧ x ≤ 1) (hload0 : 0 ≤ load) (hload1 : load ≤ 1) :
    nextFitAux items bins load = bins ∨ 0 < nextFitAuxLoad items load := by
  induction items generalizing load with
  | nil => simp [nextFitAux.eq_1]
  | cons x xs ih =>
    have hxs : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ 1 :=
      fun y hy => hitems y (List.mem_cons_of_mem x hy)
    have hx := hitems x List.mem_cons_self
    by_cases h : load + x ≤ 1
    · simp only [nextFitAux.eq_2, nextFitAuxLoad.eq_2, h, ↓reduceIte]
      exact ih (load + x) hxs (by linarith) h
    · simp only [nextFitAux.eq_2, nextFitAuxLoad.eq_2, h, ↓reduceIte]
      exact Or.inr (nextFitAuxLoad_pos xs x hxs (by linarith) hx.2)

private theorem list_sum_eq_sum_range_getD (l : List ℝ) :
    l.sum = ∑ i ∈ Finset.range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.sum_cons]
    rw [Finset.sum_range_succ' (fun i => (x :: xs).getD i 0) xs.length]
    simp only [List.getD_cons_zero]
    have hcongr : ∑ k ∈ Finset.range xs.length, (x :: xs).getD (k + 1) 0
        = ∑ k ∈ Finset.range xs.length, xs.getD k 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [List.getD_cons_succ]
    rw [hcongr, ← ih, add_comm]

private theorem list_sum_le_of_feasible (sizes : List ℝ) (B : ℕ) (a : ℕ → ℕ)
    (hfeas : FeasibleAssignment sizes B a) :
    sizes.sum ≤ (B : ℝ) := by
  rw [list_sum_eq_sum_range_getD]
  have hmaps : ∀ i ∈ Finset.range sizes.length, a i ∈ Finset.range B := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    exact hfeas.2.1 i hi
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun i => sizes.getD i 0)
  rw [← hfib]
  calc ∑ b ∈ Finset.range B, ∑ i ∈ Finset.range sizes.length with a i = b, sizes.getD i 0
      ≤ ∑ _b ∈ Finset.range B, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro b hb
        simp only [Finset.mem_range] at hb
        exact hfeas.2.2 b hb
    _ = (B : ℝ) := by simp [Finset.sum_const, Finset.card_range]

/-- Next Fit uses at most twice as many bins as any feasible packing: `B` is the bin count of
an arbitrary feasible assignment, not the optimal (least) such count, which is not defined
here. Feasibility supplies item sizes in `[0, 1]` (zero-size items included) and the
total-size bound used in the proof. -/
theorem nextFit_le_two_mul_of_feasible {sizes : List ℝ}
    {B : ℕ} {a : ℕ → ℕ} (hfeas : FeasibleAssignment sizes B a) :
    nextFitBins sizes ≤ 2 * B := by
  cases sizes with
  | nil =>
    simp only [nextFitBins]
    omega
  | cons x xs =>
    simp only [nextFitBins]
    have hitems : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ 1 :=
      fun y hy => hfeas.1 y (List.mem_cons_of_mem x hy)
    have hnonneg_xs : ∀ y ∈ xs, 0 ≤ y := fun y hy => (hitems y hy).1
    have hx := hfeas.1 x List.mem_cons_self
    have hB : a 0 < B := hfeas.2.1 0 (by simp)
    rcases nextFitAux_eq_or_load_pos xs 1 x hitems hx.1 hx.2 with hone | hloadpos
    · omega
    have hsum : (x :: xs).sum ≤ (B : ℝ) :=
      list_sum_le_of_feasible (x :: xs) B a hfeas
    have hbound := nextFitAux_bound xs 1 x hnonneg_xs
    simp only [List.sum_cons] at hsum
    have hreal : (nextFitAux xs 1 x : ℝ) < 2 * (B : ℝ) + 1 := by
      have h1 := hbound
      push_cast at h1
      have hxs_nonneg : 0 ≤ xs.sum := List.sum_nonneg hnonneg_xs
      linarith [hx.1]
    have hnat : nextFitAux xs 1 x < 2 * B + 1 := by
      have hcast : ((nextFitAux xs 1 x : ℕ) : ℝ) < (((2 * B + 1 : ℕ)) : ℝ) := by
        push_cast
        linarith
      exact Nat.cast_lt.mp hcast
    omega

end Cslib.Algorithms.Lean.Online.BinPacking
