/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.Sort.Insertion
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Choose.Basic

/-!
# Comparison cost of insertion sort

This module specializes CSLib's insertion-sort procedure to `TimeM Nat`. The explicit
`TimeM.bind` calls allow Boolean comparisons in `Type 0` and list results in any universe;
the canonical generic-monad API is restricted to `Type 0`. Equality with that API is proved
where it applies. Exactly one unit is charged for each order comparison; pattern matching,
recursive calls, and pure list construction are free. Sortedness and permutation reuse
Mathlib's `List.pairwise_insertionSort` and `List.perm_insertionSort`.
-/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type u} [LinearOrder α]

/-- **Charged comparison.** For elements $x$ and $y$ of a linearly ordered type, this
computation returns the truth value of $x \le y$ and charges one unit of time. -/
abbrev compareLE (x y : α) : TimeM Nat Bool := do
  ✓ return decide (x ≤ y)

/-- **Costed insertion into a list.** Let $a$ be an element of a linearly ordered type. Inserting
$a$ into the empty list returns $[a]$ at no cost. Inserting $a$ into a list with head $b$ and
tail $l$ first charges one unit for comparing $a \le b$; if $a \le b$ it returns $a$ followed by
$b$ and $l$, and otherwise it inserts $a$ into $l$, adding that cost, and returns $b$ followed by
the result. -/
def insertionSortInsert (a : α) : List α → TimeM Nat (List α)
  | [] => pure [a]
  | b :: xs => TimeM.bind (compareLE a b) fun before =>
      if before then pure (a :: b :: xs)
      else TimeM.bind (insertionSortInsert a xs) fun tail => pure (b :: tail)

/-- **Insertion sort with comparison cost.** On a list over a linearly ordered type, insertion
sort returns the empty list at no cost when the input is empty. On a list with head $a$ and
tail $l$, it sorts $l$ and then inserts $a$ into the result by costed insertion; its cost is the
cost of sorting $l$ plus the cost of that insertion. Exactly one unit is charged for each order
comparison. -/
def insertionSort : List α → TimeM Nat (List α)
  | [] => pure []
  | a :: xs => TimeM.bind (insertionSort xs) (insertionSortInsert a)

/-- **Costed insertion returns the ordered insertion.** For an element $a$ and a list $l$ over a
linearly ordered type, the list returned by costed insertion of $a$ into $l$ is the ordered
insertion of $a$ into $l$ with respect to $\le$: $a$ is placed immediately before the first
element $b$ of $l$ with $a \le b$, or at the end of $l$ if there is no such element. -/
theorem ret_insertionSortInsert (a : α) (xs : List α) :
    (insertionSortInsert a xs).ret = List.orderedInsert (fun x y => x ≤ y) a xs := by
  induction xs with
  | nil => simp [insertionSortInsert]
  | cons b xs ih =>
      by_cases h : a ≤ b <;>
        simp [insertionSortInsert, compareLE, TimeM.bind, List.orderedInsert_cons, h, ih]

/-- **Cost-annotated insertion sort returns the standard insertion sort.** For every list $xs$
over a linearly ordered type, the list returned by insertion sort with comparison costs equals the
standard insertion sort of $xs$ with respect to $\le$, which inserts the head into the sorted
tail. -/
@[simp]
theorem ret_insertionSort (xs : List α) :
    (insertionSort xs).ret = List.insertionSort (fun x y => x ≤ y) xs := by
  induction xs with
  | nil => simp [insertionSort]
  | cons a xs ih =>
      simpa only [insertionSort, TimeM.bind, ret_insertionSortInsert,
        List.insertionSort_cons, ih]

private theorem insertionSortInsert_eq_orderedInsertM {β : Type} [LinearOrder β]
    (a : β) (xs : List β) :
    insertionSortInsert a xs = List.orderedInsertM compareLE a xs := by
  induction xs with
  | nil => simp [insertionSortInsert]
  | cons b xs ih =>
      apply TimeM.ext <;> by_cases h : a ≤ b <;>
        simp [insertionSortInsert, List.orderedInsertM_cons, compareLE, TimeM.bind, h, ih]

/-- **Agreement with CSLib's monadic insertion sort.** For a list $l$ over a linearly ordered
type in the lowest universe, the costed insertion sort of $l$ equals CSLib's generic monadic
insertion sort run in the time-counting monad with the charged comparison: the returned lists
agree and the numbers of charged comparisons agree. -/
@[simp]
theorem insertionSort_eq_insertionSortM {β : Type} [LinearOrder β] (xs : List β) :
    insertionSort xs = List.insertionSortM compareLE xs := by
  induction xs with
  | nil => simp [insertionSort]
  | cons a xs ih =>
      apply TimeM.ext <;>
        simp [insertionSort, List.insertionSortM_cons, TimeM.bind, ih,
          insertionSortInsert_eq_orderedInsertM]

/-- **Insertion sort returns a sorted list.** For every list $l$ over a linearly ordered type,
the list returned by insertion sort on $l$ is nondecreasing. -/
theorem insertionSort_sorted (xs : List α) :
    List.Pairwise (fun x y => x ≤ y) (insertionSort xs).ret := by
  simpa using List.pairwise_insertionSort (fun x y : α => x ≤ y) xs

/-- **Insertion sort permutes its input.** For every list $l$ over a linearly ordered type, the
list returned by insertion sort is a permutation of $l$; in particular every element occurs in
it exactly as often as in $l$. -/
theorem insertionSort_perm (xs : List α) : List.Perm (insertionSort xs).ret xs := by
  simpa using List.perm_insertionSort (fun x y : α => x ≤ y) xs

/-- **Correctness of insertion sort.** For every list $l$ over a linearly ordered type, the list
returned by insertion sort is nondecreasing and is a permutation of $l$. -/
theorem insertionSort_correct (xs : List α) :
    List.Pairwise (fun x y => x ≤ y) (insertionSort xs).ret ∧
      List.Perm (insertionSort xs).ret xs :=
  ⟨insertionSort_sorted xs, insertionSort_perm xs⟩

/-- **Cost of a single insertion.** For an element $a$ and a list $l$ over a linearly ordered
type, costed insertion of $a$ into $l$ charges at most $n$ comparisons, where $n$ is the length
of $l$. -/
theorem insertionSortInsert_time_le (a : α) (xs : List α) :
    (insertionSortInsert a xs).time ≤ xs.length := by
  induction xs with
  | nil => simp [insertionSortInsert]
  | cons b xs ih =>
      by_cases h : a ≤ b
      · simp [insertionSortInsert, h, compareLE, TimeM.tick, TimeM.bind]
      · simp [insertionSortInsert, h, compareLE, TimeM.bind]
        omega

private theorem insertionSort_time_le_choose (xs : List α) :
    (insertionSort xs).time ≤ xs.length.choose 2 := by
  induction xs with
  | nil => simp [insertionSort]
  | cons a xs ih =>
      have hInsert :
          (insertionSortInsert a (insertionSort xs).ret).time ≤ xs.length := by
        calc
          (insertionSortInsert a (insertionSort xs).ret).time ≤
              (insertionSort xs).ret.length := insertionSortInsert_time_le a (insertionSort xs).ret
          _ = xs.length := (insertionSort_perm xs).length_eq
      simp only [insertionSort, TimeM.bind, List.length_cons]
      calc
        (insertionSort xs).time +
              (insertionSortInsert a (insertionSort xs).ret).time ≤
            xs.length.choose 2 + xs.length := Nat.add_le_add ih hInsert
        _ = (xs.length + 1).choose 2 := by
          simpa [Nat.choose_one_right, Nat.add_comm, Nat.succ_eq_add_one] using
            (Nat.choose_succ_succ xs.length 1).symm

/-- **Comparison bound for insertion sort.** On a list of length $n$ over a linearly ordered
type, insertion sort charges at most $n(n-1)/2$ comparisons. -/
theorem insertionSort_time (xs : List α) :
    (insertionSort xs).time ≤ xs.length * (xs.length - 1) / 2 := by
  rw [← Nat.choose_two_right]
  exact insertionSort_time_le_choose xs

end Cslib.Algorithms.Lean.TimeM
