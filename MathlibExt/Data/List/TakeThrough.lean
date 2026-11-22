/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: generalized the inclusive first-hit prefix from the ETH development to
arbitrary lists, moved it to the `List` namespace, and added importing-client tests.
-/
module

public import Mathlib.Data.List.Range

/-! # Inclusive first-hit prefixes

Adapted from `tested` and its laws in `eth/proof/threesat/Exits/Defs.lean` and
`eth/proof/threesat/Exits/Tested.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace List

/-- The prefix through the first element satisfying `p`, including that element. If no element
satisfies `p`, this is the whole list. -/
def takeThrough {α : Type*} (p : α → Bool) (xs : List α) : List α :=
  xs.take (xs.findIdx p + 1)

/-- The inclusive first-hit prefix of an empty list is empty. -/
@[simp] theorem takeThrough_nil {α : Type*} (p : α → Bool) : takeThrough p [] = [] := by
  simp [takeThrough]

/-- If the head satisfies the predicate, it is the whole inclusive first-hit prefix. -/
@[simp] theorem takeThrough_cons_of_pos {α : Type*} {p : α → Bool} {x : α}
    (h : p x = true) (xs : List α) : takeThrough p (x :: xs) = [x] := by
  simp [takeThrough, List.findIdx_cons, h]

/-- If the head does not satisfy the predicate, the search continues through the tail. -/
@[simp] theorem takeThrough_cons_of_neg {α : Type*} {p : α → Bool} {x : α}
    (h : p x = false) (xs : List α) :
    takeThrough p (x :: xs) = x :: takeThrough p xs := by
  simp [takeThrough, List.findIdx_cons, h]

/-- A singleton is its own inclusive first-hit prefix. -/
@[simp] theorem takeThrough_singleton {α : Type*} (p : α → Bool) (x : α) :
    takeThrough p [x] = [x] := by
  cases h : p x <;> simp [h]

/-- Every member of an inclusive first-hit prefix belongs to the source list. -/
theorem mem_of_mem_takeThrough {α : Type*} {p : α → Bool} {xs : List α} {x : α}
    (h : x ∈ takeThrough p xs) : x ∈ xs :=
  List.mem_of_mem_take h

/-- If no element satisfies the predicate, the inclusive first-hit prefix is the whole list. -/
theorem takeThrough_eq_self_of_any_eq_false {α : Type*} {p : α → Bool} {xs : List α}
    (h : xs.any p = false) : takeThrough p xs = xs := by
  induction xs with
  | nil => exact takeThrough_nil p
  | cons x xs ih =>
    rw [List.any_cons, Bool.or_eq_false_iff] at h
    rw [takeThrough_cons_of_neg h.1, ih h.2]

/-- Once the left list has a hit, appending another list does not change the prefix. -/
theorem takeThrough_append_of_any_eq_true {α : Type*} {p : α → Bool} {xs : List α}
    (h : xs.any p = true) (ys : List α) : takeThrough p (xs ++ ys) = takeThrough p xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases hx : p x with
    | true => rw [List.cons_append, takeThrough_cons_of_pos hx, takeThrough_cons_of_pos hx]
    | false =>
      rw [List.any_cons, hx, Bool.false_or] at h
      rw [List.cons_append, takeThrough_cons_of_neg hx, takeThrough_cons_of_neg hx, ih h]

/-- If the left list has no hit, the prefix contains all of it and continues into the right list. -/
theorem takeThrough_append_of_any_eq_false {α : Type*} {p : α → Bool} {xs : List α}
    (h : xs.any p = false) (ys : List α) :
    takeThrough p (xs ++ ys) = xs ++ takeThrough p ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.any_cons, Bool.or_eq_false_iff] at h
    rw [List.cons_append, takeThrough_cons_of_neg h.1, ih h.2, List.cons_append]

/-- The inclusive first-hit prefix has a hit exactly when the source list has one. -/
theorem any_takeThrough {α : Type*} (p : α → Bool) (xs : List α) :
    (takeThrough p xs).any p = xs.any p := by
  induction xs with
  | nil => rw [takeThrough_nil]
  | cons x xs ih =>
    cases hx : p x with
    | true => rw [takeThrough_cons_of_pos hx]; simp [hx]
    | false => rw [takeThrough_cons_of_neg hx, List.any_cons, List.any_cons, ih]

/-- On `range n`, the prefix ends one past the first hit, or at `n` if there is no hit. -/
theorem takeThrough_range (q : Nat → Bool) (n : Nat) :
    takeThrough q (range n) =
      range (match (range n).find? q with | some i => i + 1 | none => n) := by
  unfold takeThrough
  rw [List.take_range]
  congr 1
  cases h : (List.range n).find? q with
  | none =>
    rw [List.find?_eq_none] at h
    rw [List.findIdx_eq_length_of_false (fun x hx => by simpa using h x hx), List.length_range]
    change min (n + 1) n = n
    omega
  | some i =>
    rw [List.find?_range_eq_some] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    have hi := List.mem_range.1 h₂
    rw [(List.findIdx_eq (p := q) (xs := List.range n) (i := i) (by simpa using hi)).2
      ⟨by simpa using h₁, fun j hj => by simpa using h₃ j hj⟩]
    change min (i + 1) n = i + 1
    omega

/-- Filtering selected elements from an inclusive prefix commutes with taking the corresponding
inclusive prefix of the selected elements. -/
theorem filterMap_takeThrough {α β : Type*} (sel : α → Option β) (p : β → Bool)
    (xs : List α) :
    (takeThrough (fun x => (sel x).any p) xs).filterMap sel =
      takeThrough p (xs.filterMap sel) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases h : sel x with
    | none =>
      have hx : (sel x).any p = false := by simp [h]
      rw [takeThrough_cons_of_neg (p := fun x => (sel x).any p) hx,
        List.filterMap_cons_none h,
        List.filterMap_cons_none h, ih]
    | some y =>
      cases hy : p y with
      | true =>
        have hx : (sel x).any p = true := by simp [h, hy]
        rw [takeThrough_cons_of_pos (p := fun x => (sel x).any p) hx,
          List.filterMap_cons_some h,
          List.filterMap_cons_some h, takeThrough_cons_of_pos hy]
        rfl
      | false =>
        have hx : (sel x).any p = false := by simp [h, hy]
        rw [takeThrough_cons_of_neg (p := fun x => (sel x).any p) hx,
          List.filterMap_cons_some h,
          List.filterMap_cons_some h, takeThrough_cons_of_neg hy, ih]

end List
