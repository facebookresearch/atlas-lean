/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# Double-ended queues

A `Deque` is represented by two lists. The `front` list stores the front part of the sequence
in order, so its head is the frontmost element. The `back` list stores the back part of the
sequence in reverse order, so its head is the backmost element. The represented sequence is
therefore `front ++ back.reverse`.

Pushing at either end conses onto the corresponding list. Popping at an end whose list is
empty reverses the other list, following Lean's two-list `Std.Queue`; peeking at such an end
only traverses the other list with `getLast?` and allocates nothing. This file proves
that every operation agrees with the represented sequence; it makes no complexity claims.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/-- A two-list double-ended queue: `front` is in order and `back` is stored reversed. -/
structure Deque (α : Type u) where
  front : List α
  back : List α

namespace Deque

variable {α : Type u}

/-- The sequence represented by a deque, from front to back. -/
def contents (d : Deque α) : List α :=
  d.front ++ d.back.reverse

/-- The deque containing no elements. -/
def empty : Deque α :=
  ⟨[], []⟩

@[simp]
theorem contents_empty : contents (empty : Deque α) = [] :=
  rfl

/-- A deque reports that it is empty when both of its lists are empty. -/
def isEmpty (d : Deque α) : Bool :=
  d.front.isEmpty && d.back.isEmpty

/-- A deque reports that it is empty exactly when its represented sequence is empty. -/
@[simp]
theorem isEmpty_eq_true_iff (d : Deque α) :
    d.isEmpty = true ↔ contents d = [] := by
  cases d with
  | mk front back => simp [isEmpty, contents, Bool.and_eq_true, List.isEmpty_iff]

/-- Add an element at the front of a deque. -/
def pushFront (d : Deque α) (value : α) : Deque α :=
  ⟨value :: d.front, d.back⟩

/-- Pushing at the front conses onto the represented sequence. -/
@[simp]
theorem contents_pushFront (d : Deque α) (value : α) :
    contents (d.pushFront value) = value :: contents d :=
  rfl

/-- Add an element at the back of a deque. -/
def pushBack (d : Deque α) (value : α) : Deque α :=
  ⟨d.front, value :: d.back⟩

/-- Pushing at the back appends to the represented sequence. -/
@[simp]
theorem contents_pushBack (d : Deque α) (value : α) :
    contents (d.pushBack value) = contents d ++ [value] := by
  simp [pushBack, contents, List.append_assoc]

/-- Observe the front element without removing it, or `none` when the deque is empty. -/
def peekFront : Deque α → Option α
  | ⟨value :: _, _⟩ => some value
  | ⟨[], back⟩ => back.getLast?

/-- Peeking at the front returns the head of the represented sequence. -/
@[simp]
theorem peekFront_eq_head (d : Deque α) : d.peekFront = (contents d).head? := by
  cases d with
  | mk front back =>
      cases front with
      | nil => simp [peekFront, contents, List.head?_reverse]
      | cons value front' => rfl

/-- Observe the back element without removing it, or `none` when the deque is empty. -/
def peekBack : Deque α → Option α
  | ⟨_, value :: _⟩ => some value
  | ⟨front, []⟩ => front.getLast?

/-- Peeking at the back returns the last element of the represented sequence. -/
@[simp]
theorem peekBack_eq_getLast (d : Deque α) : d.peekBack = (contents d).getLast? := by
  cases d with
  | mk front back =>
      cases back with
      | nil => simp [peekBack, contents]
      | cons value back' => simp [peekBack, contents]

/-- Remove and return the front element, or `none` when the deque is empty. -/
def popFront : Deque α → Option (α × Deque α)
  | ⟨value :: front', back⟩ => some (value, ⟨front', back⟩)
  | ⟨[], back⟩ =>
      match back.reverse with
      | [] => none
      | value :: rest => some (value, ⟨rest, []⟩)

/-- Popping the front fails exactly when the represented sequence is empty. -/
@[simp]
theorem popFront_eq_none_iff (d : Deque α) :
    d.popFront = none ↔ contents d = [] := by
  cases d with
  | mk front back =>
      cases front with
      | cons value front' => simp [popFront, contents]
      | nil => cases h : back.reverse <;> simp [popFront, contents, h]

/-- A successful front pop returns the head and a deque representing the remaining tail. -/
theorem contents_eq_cons_of_popFront_eq_some
    {d : Deque α} {head : α} {rest : Deque α}
    (h : d.popFront = some (head, rest)) :
    contents d = head :: contents rest := by
  cases d with
  | mk front back =>
      cases front with
      | cons value front' =>
          simp [popFront] at h
          obtain ⟨hhead, hrest⟩ := h
          cases hhead
          cases hrest
          rfl
      | nil =>
          cases hr : back.reverse with
          | nil => simp [popFront, hr] at h
          | cons value rest' =>
              simp [popFront, hr] at h
              obtain ⟨hhead, hrest⟩ := h
              cases hhead
              cases hrest
              simpa [contents] using hr

/-- Remove and return the back element, or `none` when the deque is empty. -/
def popBack : Deque α → Option (α × Deque α)
  | ⟨front, value :: back'⟩ => some (value, ⟨front, back'⟩)
  | ⟨front, []⟩ =>
      match front.reverse with
      | [] => none
      | value :: rest => some (value, ⟨[], rest⟩)

/-- Popping the back fails exactly when the represented sequence is empty. -/
@[simp]
theorem popBack_eq_none_iff (d : Deque α) :
    d.popBack = none ↔ contents d = [] := by
  cases d with
  | mk front back =>
      cases back with
      | cons value back' => simp [popBack, contents]
      | nil =>
          cases h : front.reverse with
          | nil =>
              have hfront : front = [] := by
                have hrev := congrArg List.reverse h
                simpa using hrev
              simp [popBack, contents, hfront]
          | cons value rest' =>
              have hfront : front ≠ [] := by
                rintro rfl
                simp at h
              simp [popBack, contents, h, hfront]

/-- A successful back pop returns the last element and a deque for the remaining prefix. -/
theorem contents_eq_append_of_popBack_eq_some
    {d : Deque α} {last : α} {rest : Deque α}
    (h : d.popBack = some (last, rest)) :
    contents d = contents rest ++ [last] := by
  cases d with
  | mk front back =>
      cases back with
      | cons value back' =>
          simp [popBack] at h
          obtain ⟨hlast, hrest⟩ := h
          cases hlast
          cases hrest
          simp [contents, List.append_assoc]
      | nil =>
          cases hr : front.reverse with
          | nil => simp [popBack, hr] at h
          | cons value rest' =>
              simp [popBack, hr] at h
              obtain ⟨hlast, hrest⟩ := h
              cases hlast
              cases hrest
              have hfront : front = rest'.reverse ++ [last] := by
                have hrev := congrArg List.reverse hr
                simpa using hrev
              simp [contents, hfront]

end Deque

end Cslib.Algorithms.Lean
