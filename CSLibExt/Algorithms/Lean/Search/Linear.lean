/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM

/-!
# Linear search with comparison cost

This module implements predicate-based linear search on lists and charges one unit for each
predicate evaluation. List pattern matching, index arithmetic, recursive calls, and construction
of the result are free. The returned index is related to Lean's `List.findIdx?`.

The algorithm follows the sequential scan in Cormen, Leiserson, Rivest, and Stein,
*Introduction to Algorithms*, third edition, Section 2.1, Exercise 2.1-3. The predicate-based
interface and exact successful-search costs are refinements made explicit here; the source states
the equality-search problem but does not give these exact formulas.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u}

/-- Returns the index of the first element satisfying `p`, charging one unit per evaluation of
`p`. No cost is charged for list operations, index arithmetic, or control flow. -/
def linearSearch (p : α → Bool) : List α → TimeM Nat (Option Nat)
  | [] => pure none
  | x :: xs => do
      ✓
      if p x then
        return some 0
      else
        return (← linearSearch p xs).map (· + 1)

/-- Erasing the recorded cost recovers Lean's standard first-index search. -/
@[simp]
theorem ret_linearSearch (p : α → Bool) (xs : List α) :
    (linearSearch p xs).ret = xs.findIdx? p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : p x <;> simp [linearSearch, List.findIdx?_cons, h, ih]

/-- A successful search returns exactly the first satisfying index. -/
theorem linearSearch_eq_some_iff (p : α → Bool) (xs : List α) (i : Nat) :
    (linearSearch p xs).ret = some i ↔
      ∃ h : i < xs.length,
        p xs[i] = true ∧
          ∀ j (hji : j < i), p (xs[j]'(Nat.lt_trans hji h)) = false := by
  rw [ret_linearSearch]
  simpa only [Bool.not_eq_true] using
    (List.findIdx?_eq_some_iff_getElem (xs := xs) (p := p) (i := i))

/-- Search fails exactly when no list element satisfies the predicate. -/
theorem linearSearch_eq_none_iff (p : α → Bool) (xs : List α) :
    (linearSearch p xs).ret = none ↔ ∀ x ∈ xs, p x = false := by
  rw [ret_linearSearch]
  exact List.findIdx?_eq_none_iff

/-- Searching an empty list evaluates the predicate zero times. -/
@[simp]
theorem linearSearch_time_nil (p : α → Bool) : (linearSearch p []).time = 0 := rfl

/-- The explicit unit-cost recurrence: the head predicate costs one unit, and the tail is searched
only when the head fails. -/
theorem linearSearch_time_cons (p : α → Bool) (x : α) (xs : List α) :
    (linearSearch p (x :: xs)).time =
      if p x then 1 else 1 + (linearSearch p xs).time := by
  cases h : p x <;> simp [linearSearch, h]

private lemma linearSearch_time_eq (p : α → Bool) (xs : List α) :
    (linearSearch p xs).time =
      match xs.findIdx? p with
      | some i => i + 1
      | none => xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hp : p x with
      | true => simp [linearSearch_time_cons, List.findIdx?_cons, hp]
      | false =>
          rw [linearSearch_time_cons]
          simp only [hp, Bool.false_eq_true, ↓reduceIte, List.findIdx?_cons]
          rw [ih]
          cases xs.findIdx? p <;> simp [Nat.add_comm]

/-- A successful search at index `i` performs exactly `i + 1` predicate evaluations. -/
theorem linearSearch_time_eq_of_ret_eq_some (p : α → Bool) (xs : List α) (i : Nat)
    (h : (linearSearch p xs).ret = some i) :
    (linearSearch p xs).time = i + 1 := by
  have hidx : xs.findIdx? p = some i := by simpa only [ret_linearSearch] using h
  rw [linearSearch_time_eq, hidx]

/-- An unsuccessful search evaluates the predicate once for every list element. -/
theorem linearSearch_time_eq_of_ret_eq_none (p : α → Bool) (xs : List α)
    (h : (linearSearch p xs).ret = none) :
    (linearSearch p xs).time = xs.length := by
  have hidx : xs.findIdx? p = none := by simpa only [ret_linearSearch] using h
  rw [linearSearch_time_eq, hidx]

/-- Linear search evaluates the predicate at most once for every list element. -/
theorem linearSearch_time_le (p : α → Bool) (xs : List α) :
    (linearSearch p xs).time ≤ xs.length := by
  rw [linearSearch_time_eq]
  cases hidx : xs.findIdx? p with
  | none => exact Nat.le_refl _
  | some i =>
      have hi : i < xs.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp hidx).1
      exact Nat.lt_iff_add_one_le.mp hi

end Cslib.Algorithms.Lean.TimeM
