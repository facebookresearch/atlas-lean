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

/-- **Linear search.** Given a predicate $p$ on a type $\alpha$ and a list $L$ of elements of
$\alpha$, linear search scans $L$ from the front and returns the index of the first element of $L$
that satisfies $p$, or no index if no element does, together with a cost that counts one unit for
each evaluation of $p$. On the empty list it returns no index at cost $0$. On a list with head $x$
and tail $T$ it evaluates $p(x)$ at a cost of one unit; if $p(x)$ is true it returns the index $0$,
and otherwise it searches $T$, adds one to the index found there (if any), and adds the cost of
that search.

No cost is charged for list operations, index arithmetic, or control flow. -/
def linearSearch (p : α → Bool) : List α → TimeM Nat (Option Nat)
  | [] => pure none
  | x :: xs => do
      ✓
      if p x then
        return some 0
      else
        return (← linearSearch p xs).map (· + 1)

/-- **Linear search returns the first satisfying index.** For every predicate $p$ on a type
$\alpha$ and every list $L = (x_0, \dots, x_{n-1})$ over $\alpha$, the index returned by linear
search for $p$ on $L$ (ignoring its cost) equals the result of the standard library's
first-index search: the least $i < n$ with $p(x_i)$ true, or no index if $p(x_i)$ is false for
every $i < n$. -/
@[simp]
theorem ret_linearSearch (p : α → Bool) (xs : List α) :
    (linearSearch p xs).ret = xs.findIdx? p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : p x <;> simp [linearSearch, List.findIdx?_cons, h, ih]

/-- **Characterization of a successful linear search.** For every predicate $p$ on a type
$\alpha$, every list $L = (x_0, \dots, x_{n-1})$ over $\alpha$ and every natural number $i$,
linear search for $p$ on $L$ returns the index $i$ if and only if $i < n$, $p(x_i)$ is true, and
$p(x_j)$ is false for every $j < i$. -/
theorem linearSearch_eq_some_iff (p : α → Bool) (xs : List α) (i : Nat) :
    (linearSearch p xs).ret = some i ↔
      ∃ h : i < xs.length,
        p xs[i] = true ∧
          ∀ j (hji : j < i), p (xs[j]'(Nat.lt_trans hji h)) = false := by
  rw [ret_linearSearch]
  simpa only [Bool.not_eq_true] using
    (List.findIdx?_eq_some_iff_getElem (xs := xs) (p := p) (i := i))

/-- **Linear search fails exactly when no element satisfies the predicate.** For every predicate
$p$ on a type $\alpha$ and every list $L$ over $\alpha$, linear search for $p$ on $L$ returns no
index if and only if $p(x)$ is false for every element $x$ of $L$. -/
theorem linearSearch_eq_none_iff (p : α → Bool) (xs : List α) :
    (linearSearch p xs).ret = none ↔ ∀ x ∈ xs, p x = false := by
  rw [ret_linearSearch]
  exact List.findIdx?_eq_none_iff

/-- **Cost of linear search on the empty list.** For every predicate $p$ on a type $\alpha$, linear
search for $p$ on the empty list has cost $0$: it evaluates $p$ zero times. -/
@[simp]
theorem linearSearch_time_nil (p : α → Bool) : (linearSearch p []).time = 0 := rfl

/-- **Cost recurrence for linear search.** For every predicate $p$ on a type $\alpha$, every
$x \in \alpha$ and every list $T$ over $\alpha$, the cost of linear search for $p$ on the list
with head $x$ and tail $T$ is $1$ if $p(x)$ is true, and $1$ plus the cost of linear search for
$p$ on $T$ if $p(x)$ is false. The head costs one evaluation of $p$, and the tail is searched only
when the head fails. -/
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

/-- **Cost of a successful linear search.** For every predicate $p$ on a type $\alpha$, every
list $L$ over $\alpha$ and every natural number $i$, if linear search for $p$ on $L$ returns the
index $i$, then its cost is $i + 1$: it evaluates $p$ exactly $i + 1$ times. -/
theorem linearSearch_time_eq_of_ret_eq_some (p : α → Bool) (xs : List α) (i : Nat)
    (h : (linearSearch p xs).ret = some i) :
    (linearSearch p xs).time = i + 1 := by
  have hidx : xs.findIdx? p = some i := by simpa only [ret_linearSearch] using h
  rw [linearSearch_time_eq, hidx]

/-- **Cost of an unsuccessful linear search.** For every predicate $p$ on a type $\alpha$ and
every list $L$ over $\alpha$, if linear search for $p$ on $L$ returns no index, then its cost is
the length of $L$: it evaluates $p$ once for every element of $L$. -/
theorem linearSearch_time_eq_of_ret_eq_none (p : α → Bool) (xs : List α)
    (h : (linearSearch p xs).ret = none) :
    (linearSearch p xs).time = xs.length := by
  have hidx : xs.findIdx? p = none := by simpa only [ret_linearSearch] using h
  rw [linearSearch_time_eq, hidx]

/-- **Linear search costs at most the list length.** For every predicate $p$ on a type $\alpha$
and every list $L$ over $\alpha$, the cost of linear search for $p$ on $L$ is at most the length
of $L$: it evaluates $p$ at most once for every element of $L$. -/
theorem linearSearch_time_le (p : α → Bool) (xs : List α) :
    (linearSearch p xs).time ≤ xs.length := by
  rw [linearSearch_time_eq]
  cases hidx : xs.findIdx? p with
  | none => exact Nat.le_refl _
  | some i =>
      have hi : i < xs.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp hidx).1
      exact Nat.lt_iff_add_one_le.mp hi

end Cslib.Algorithms.Lean.TimeM
