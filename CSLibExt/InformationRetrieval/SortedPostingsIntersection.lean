/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.InformationRetrieval.BooleanRetrieval
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Order.Compare
import Mathlib.Data.List.Pairwise

/-!
# Sorted postings intersection

C. D. Manning, P. Raghavan and H. Schütze, *Introduction to Information Retrieval*
(Cambridge University Press, 2008), §1.3, Figure 1.6 and the following discussion, describe
how to intersect postings lists sorted in a common document order: advance the smaller head,
or emit the common head and advance both. See the authors' HTML edition:
<https://nlp.stanford.edu/IR-book/html/htmledition/processing-boolean-queries-1.html>.

`intersectPostings` implements the two pointers as list suffixes. For `buildIndex`, the
common order is that of `Fin N`; repeated occurrences of a term in a document do not change
its membership.

The book gives a linear work bound. Here `TimeM.time` counts one three-way head comparison
per iteration, not the operations inside `cmp`. The bound `x + y - 1` for nonempty lists of
lengths `x` and `y` is derived from the loop. An alternative that tests equality first and
then tests order **only on unequal heads** visits the same pairs: it uses one test on a tie
and two otherwise, hence at most `2 * (x + y - 1)` tests. Neither count measures wall time.
-/

@[expose] public section

namespace Cslib.InformationRetrieval

open Cslib.Algorithms.Lean

variable {α : Type*} [LinearOrder α]

/-- Two-pointer intersection on lists over one linear order. `ret` emits a head exactly on
an equality branch; `time` counts the three-way head classifications that guide the recursion.
Stopping on either empty input costs nothing. -/
def intersectPostings : List α → List α → TimeM ℕ (List α)
  | [], _ | _ :: _, [] => pure []
  | a :: as, b :: bs => do
    TimeM.tick 1
    match cmp a b with
    | .lt => intersectPostings as (b :: bs)
    | .eq => List.cons a <$> intersectPostings as bs
    | .gt => intersectPostings (a :: as) bs
termination_by xs ys => xs.length + ys.length

/-- An empty left input returns no elements and incurs no comparisons. -/
@[simp] theorem intersectPostings_nil_left (ys : List α) :
    intersectPostings [] ys = pure [] := by
  rw [intersectPostings]

/-- An empty right input returns no elements and incurs no comparisons. -/
@[simp] theorem intersectPostings_nil_right (xs : List α) :
    intersectPostings xs [] = pure [] := by
  cases xs <;> rw [intersectPostings]

/-- Without any ordering hypothesis on the lists, the output is a sublist of the left input. -/
theorem intersectPostings_sublist_left (xs ys : List α) :
    (intersectPostings xs ys).ret.Sublist xs := by
  fun_induction intersectPostings xs ys with
  | case1 => simp
  | case2 => simp
  | case3 a as b bs ihlt iheq ihgt =>
    simp only [TimeM.ret_bind]
    cases cmp a b with
    | lt => exact ihlt.cons a
    | eq => exact iheq.cons_cons a
    | gt => exact ihgt

/-- The merge preserves strict increase of the left input, even if the right input is unsorted. -/
theorem intersectPostings_pairwise_lt {xs ys : List α} (hx : xs.Pairwise (· < ·)) :
    (intersectPostings xs ys).ret.Pairwise (· < ·) :=
  hx.sublist (intersectPostings_sublist_left xs ys)

/-- For nondecreasing inputs in the same order, the output contains an element if and only if
both lists contain it. For strictly increasing postings this, together with strict increase
of the output, says that every common element occurs exactly once. -/
theorem mem_intersectPostings {xs ys : List α} (hx : xs.Pairwise (· ≤ ·))
    (hy : ys.Pairwise (· ≤ ·)) (z : α) :
    z ∈ (intersectPostings xs ys).ret ↔ z ∈ xs ∧ z ∈ ys := by
  fun_induction intersectPostings xs ys with
  | case1 => simp
  | case2 => simp
  | case3 a as b bs ihlt iheq ihgt =>
    simp only [TimeM.ret_bind]
    cases h : cmp a b with
    | lt =>
      have ha : a ∉ b :: bs := fun hm => ((cmp_eq_lt_iff a b).mp h).not_ge (hy.rel_head hm)
      rw [ihlt hx.tail hy]
      grind only [List.mem_cons]
    | eq =>
      obtain rfl := (cmp_eq_eq_iff a b).mp h
      simp [iheq hx.tail hy.tail, or_and_left]
    | gt =>
      have hb : b ∉ a :: as := fun hm => ((cmp_eq_gt_iff a b).mp h).not_ge (hx.rel_head hm)
      rw [ihgt hx hy.tail]
      grind only [List.mem_cons]

/-- With a strictly increasing left input and a nondecreasing right input, each common element
occurs once in the result and every other element occurs zero times. -/
theorem count_intersectPostings {xs ys : List α} (hx : xs.Pairwise (· < ·))
    (hy : ys.Pairwise (· ≤ ·)) (z : α) :
    (intersectPostings xs ys).ret.count z = if z ∈ xs ∧ z ∈ ys then 1 else 0 := by
  have hm := mem_intersectPostings (hx.imp le_of_lt) hy z
  split
  next h =>
    exact List.count_eq_one_of_mem ((intersectPostings_pairwise_lt hx).imp ne_of_lt) (hm.mpr h)
  next h => exact List.count_eq_zero.mpr (mt hm.mp h)

/-- For arbitrary input lists of lengths `x` and `y`, the merge makes at most `x + y - 1`
three-way comparisons, with natural-number subtraction. No sortedness assumption is needed. -/
theorem intersectPostings_time_le (xs ys : List α) :
    (intersectPostings xs ys).time ≤ xs.length + ys.length - 1 := by
  fun_induction intersectPostings xs ys with
  | case1 => simp
  | case2 => simp
  | case3 a as b bs ihlt iheq ihgt =>
    simp only [TimeM.time_bind, TimeM.time_tick, List.length_cons] at *
    cases cmp a b <;> simp only [TimeM.time_map] <;> omega

/-- Intersecting the two lists from a built inverted index returns a document exactly when it
belongs to both term sets, for any finite corpus of term multisets and terms with decidable
equality. Document indices use the same zero-based `Fin N` as `buildIndex`. -/
theorem mem_intersectPostings_buildIndex {N : ℕ} {τ : Type*} [DecidableEq τ]
    (corpus : Corpus N τ) (s t : τ) (d : Fin N) :
    d ∈ (intersectPostings (buildIndex corpus s) (buildIndex corpus t)).ret ↔
      d ∈ docsWith corpus s ∧ d ∈ docsWith corpus t := by
  unfold buildIndex
  rw [mem_intersectPostings ((postings_pairwise_lt corpus s).imp le_of_lt)
    ((postings_pairwise_lt corpus t).imp le_of_lt)]
  simp only [← postings_toFinset, List.mem_toFinset]

end Cslib.InformationRetrieval
