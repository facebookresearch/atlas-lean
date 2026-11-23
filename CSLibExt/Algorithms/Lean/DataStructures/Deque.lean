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

/-- **Two-list deque.** A deque with elements in a type $\alpha$ consists of two lists of elements
of $\alpha$, the front list and the back list. The front list holds the front part of the
sequence in order and the back list holds the back part in reverse order. -/
structure Deque (α : Type u) where
  front : List α
  back : List α

namespace Deque

variable {α : Type u}

/-- **Represented sequence of a deque.** The sequence represented by a deque with front list $f$
and back list $b$ is $f$ followed by the reverse of $b$; it lists the elements from front to
back. -/
def contents (d : Deque α) : List α :=
  d.front ++ d.back.reverse

/-- **The empty deque.** The empty deque is the deque whose front list and back list are both
empty. -/
def empty : Deque α :=
  ⟨[], []⟩

@[simp]
theorem contents_empty : contents (empty : Deque α) = [] :=
  rfl

/-- **Emptiness test for a deque.** The emptiness test of a deque returns true exactly when both
its front list and its back list are empty. -/
def isEmpty (d : Deque α) : Bool :=
  d.front.isEmpty && d.back.isEmpty

/-- **Correctness of the deque emptiness test.** For every deque $d$, the emptiness test of $d$
returns true if and only if the sequence represented by $d$ is empty. -/
@[simp]
theorem isEmpty_eq_true_iff (d : Deque α) :
    d.isEmpty = true ↔ contents d = [] := by
  cases d with
  | mk front back => simp [isEmpty, contents, Bool.and_eq_true, List.isEmpty_iff]

/-- **Push at the front of a deque.** Let $d$ be a deque with front list $f$ and back list $b$,
where $b$ is stored in reverse order. Pushing an element $x$ at the front of $d$ gives the deque
with front list consisting of $x$ followed by the entries of $f$, and back list $b$. -/
def pushFront (d : Deque α) (value : α) : Deque α :=
  ⟨value :: d.front, d.back⟩

/-- **Pushing at the front of a deque.** For every deque $d$ and element $x$, the sequence
represented by the deque obtained by pushing $x$ at the front of $d$ is $x$ followed by the
sequence represented by $d$. -/
@[simp]
theorem contents_pushFront (d : Deque α) (value : α) :
    contents (d.pushFront value) = value :: contents d :=
  rfl

/-- **Push at the back of a deque.** Let $d$ be a deque with front list $f$ and back list $b$,
where $b$ is stored in reverse order. Pushing an element $x$ at the back of $d$ gives the deque
with front list $f$ and back list consisting of $x$ followed by the entries of $b$. -/
def pushBack (d : Deque α) (value : α) : Deque α :=
  ⟨d.front, value :: d.back⟩

/-- **Pushing at the back of a deque.** For every deque $d$ and element $x$, the sequence
represented by the deque obtained by pushing $x$ at the back of $d$ is the sequence represented by
$d$ followed by $x$. -/
@[simp]
theorem contents_pushBack (d : Deque α) (value : α) :
    contents (d.pushBack value) = contents d ++ [value] := by
  simp [pushBack, contents, List.append_assoc]

/-- **Peek at the front of a deque.** Let $d$ be a deque with front list $f$ and back list $b$,
where $b$ is stored in reverse order. Peeking at the front of $d$ returns, without removing it,
the first element of $f$ when $f$ is nonempty, and otherwise the last element of $b$; when both
lists are empty it returns no element. -/
def peekFront : Deque α → Option α
  | ⟨value :: _, _⟩ => some value
  | ⟨[], back⟩ => back.getLast?

/-- **Peeking at the front gives the first element.** For every deque $d$, peeking at the front of
$d$ returns the first element of the sequence represented by $d$, and returns no element when
that sequence is empty. -/
@[simp]
theorem peekFront_eq_head (d : Deque α) : d.peekFront = (contents d).head? := by
  cases d with
  | mk front back =>
      cases front with
      | nil => simp [peekFront, contents, List.head?_reverse]
      | cons value front' => rfl

/-- **Peek at the back of a deque.** Let $d$ be a deque with front list $f$ and back list $b$,
where $b$ is stored in reverse order. Peeking at the back of $d$ returns, without removing it,
the first element of $b$ when $b$ is nonempty, and otherwise the last element of $f$; when both
lists are empty it returns no element. -/
def peekBack : Deque α → Option α
  | ⟨_, value :: _⟩ => some value
  | ⟨front, []⟩ => front.getLast?

/-- **Peeking at the back of a deque.** For every deque $d$, peeking at the back of $d$ returns
the last element of the sequence represented by $d$ when that sequence is nonempty, and returns
nothing when it is empty. -/
@[simp]
theorem peekBack_eq_getLast (d : Deque α) : d.peekBack = (contents d).getLast? := by
  cases d with
  | mk front back =>
      cases back with
      | nil => simp [peekBack, contents]
      | cons value back' => simp [peekBack, contents]

/-- **Pop the front of a deque.** Let $d$ be a deque with front list $f$ and back list $b$, where
$b$ is stored in reverse order. If $f$ has first element $v$ and remaining list $f'$, popping the
front of $d$ returns $v$ together with the deque with front list $f'$ and back list $b$. If $f$ is
empty and the reverse of $b$ has first element $v$ and remaining list $r$, it returns $v$ together
with the deque with front list $r$ and empty back list. If both lists are empty, it returns no
result. -/
def popFront : Deque α → Option (α × Deque α)
  | ⟨value :: front', back⟩ => some (value, ⟨front', back⟩)
  | ⟨[], back⟩ =>
      match back.reverse with
      | [] => none
      | value :: rest => some (value, ⟨rest, []⟩)

/-- **Popping the front fails exactly on empty deques.** For every deque $d$, popping the front of
$d$ returns no result if and only if the sequence represented by $d$ is empty. -/
@[simp]
theorem popFront_eq_none_iff (d : Deque α) :
    d.popFront = none ↔ contents d = [] := by
  cases d with
  | mk front back =>
      cases front with
      | cons value front' => simp [popFront, contents]
      | nil => cases h : back.reverse <;> simp [popFront, contents, h]

/-- **Popping the front of a deque.** If popping the front of a deque $d$ succeeds and returns an
element $x$ and a deque $d'$, then the sequence represented by $d$ is $x$ followed by the sequence
represented by $d'$. -/
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

/-- **Pop the back of a deque.** Let $d$ be a deque with front list $f$ and back list $b$, where
$b$ is stored in reverse order. If $b$ has first element $v$ and remaining list $b'$, popping the
back of $d$ returns $v$ together with the deque with front list $f$ and back list $b'$. If $b$ is
empty and the reverse of $f$ has first element $v$ and remaining list $r$, it returns $v$ together
with the deque with empty front list and back list $r$. If both lists are empty, it returns no
result. -/
def popBack : Deque α → Option (α × Deque α)
  | ⟨front, value :: back'⟩ => some (value, ⟨front, back'⟩)
  | ⟨front, []⟩ =>
      match front.reverse with
      | [] => none
      | value :: rest => some (value, ⟨[], rest⟩)

/-- **Popping the back fails exactly on empty deques.** For every deque $d$, popping the back of
$d$ returns no result if and only if the sequence represented by $d$ is empty. -/
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

/-- **Popping the back of a deque.** If popping the back of a deque $d$ succeeds and returns an
element $x$ and a deque $d'$, then the sequence represented by $d$ is the sequence represented by
$d'$ followed by $x$. -/
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
