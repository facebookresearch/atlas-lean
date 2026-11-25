/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Defs.LinearOrder

/-!
# Ordered insertion into a list

`orderedInsert x xs` inserts `x` into `xs` at its sorted position. On a
strictly sorted list (`xs.Pairwise (· < ·)`) this returns `xs` unchanged
when `x` is already present (`orderedInsert_eq_of_mem`); on an arbitrary
list the scan stops at the first element not smaller than `x`, so a
duplicate occurring later is not detected — for example
`orderedInsert 2 [3, 2] = [2, 3, 2]`. The tree implementations in this
library (2-3 trees and B-trees) only apply it to strictly sorted
flattenings, whose flattening lemmas state that tree insertion acts on
the inorder flattening by `orderedInsert`.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean

variable {α : Type u}

/-- **Ordered insertion into a list.** For an element $x$ of a linearly ordered type, the ordered
insertion of $x$ into the empty list is $[x]$. For a list with head $a$ and tail $\ell$, it is
$x$ followed by the whole list if $x < a$; it is $a$ followed by the ordered insertion of $x$
into $\ell$ if $a < x$; and it is the list unchanged if $a = x$.

On a strictly increasing list a key that is already present is therefore ignored. On an unsorted
list a later duplicate is not detected: inserting $2$ into $[3, 2]$ gives $[2, 3, 2]$. -/
public def orderedInsert [LinearOrder α] (x : α) : List α → List α
  | [] => [x]
  | a :: as =>
      if x < a then x :: a :: as
      else if a < x then a :: orderedInsert x as
      else a :: as

/-- **Members after ordered insertion.** Over a linearly ordered type, for all elements $x$, $y$
and every list $\ell$, the element $y$ belongs to the ordered insertion of $x$ into $\ell$ if and
only if $y = x$ or $y$ belongs to $\ell$. -/
public theorem mem_orderedInsert [LinearOrder α] {x y : α} {xs : List α} :
    y ∈ orderedInsert x xs ↔ y = x ∨ y ∈ xs := by
  induction xs with
  | nil => simp [orderedInsert]
  | cons a as ih =>
    by_cases hxa : x < a
    · simp [orderedInsert, hxa]
    · by_cases hax : a < x
      · simp [orderedInsert, hxa, hax, ih, or_left_comm]
      · have hEq : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        subst hEq
        simp [orderedInsert, hxa]

/-- **Inserting a present element into a strictly increasing list.** Over a linearly ordered
type, if every element of a list $\ell$ is smaller than every later element of $\ell$ and $x$
belongs to $\ell$, then the ordered insertion of $x$ into $\ell$ is $\ell$ itself.

Without strict increase this fails: inserting $2$ into $[3, 2]$ gives $[2, 3, 2]$. -/
public theorem orderedInsert_eq_of_mem [LinearOrder α] {x : α} {xs : List α}
    (hSorted : xs.Pairwise (· < ·)) (hMem : x ∈ xs) :
    orderedInsert x xs = xs := by
  induction xs with
  | nil => simp at hMem
  | cons a as ih =>
      rw [List.pairwise_cons] at hSorted
      cases hMem with
      | head =>
          have hxx : ¬ x < x := lt_irrefl x
          simp [orderedInsert, hxx]
      | tail _ hMemAs =>
          have hax : a < x := hSorted.1 x hMemAs
          simp [orderedInsert, hax, not_lt.mpr (le_of_lt hax),
            ih hSorted.2 hMemAs]

end Cslib.Algorithms.Lean
