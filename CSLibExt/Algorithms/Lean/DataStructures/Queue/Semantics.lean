/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Init.Data.Queue

import all Init.Data.Queue

/-!
# FIFO semantics for `Std.Queue`

This file exposes the logical FIFO sequence represented by Lean's two-list queue and proves the
behavior of the basic queue operations against that sequence. It makes no complexity claims.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Queue

universe u

variable {α : Type u}

/-- **Contents of a two-list queue.** A queue is stored as a dequeue list and an enqueue list
whose most recently enqueued element comes first. Its contents are its elements in FIFO
order: the dequeue list followed by the reverse of the enqueue list. -/
def contents (q : Std.Queue α) : List α :=
  q.dList ++ q.eList.reverse

@[simp]
theorem contents_empty : contents (Std.Queue.empty : Std.Queue α) = [] := by
  rfl

/-- **Array conversion lists the contents.** For every queue $q$, the array obtained from $q$,
read as a list, equals the contents of $q$. -/
@[simp]
theorem toArray_toList (q : Std.Queue α) : q.toArray.toList = contents q := by
  simp [Std.Queue.toArray, contents]

/-- **Enqueueing appends to the contents.** For every queue $q$ and value $v$, the contents of
the queue obtained by enqueueing $v$ onto $q$ are the contents of $q$ followed by $v$. -/
@[simp]
theorem contents_enqueue (q : Std.Queue α) (value : α) :
    contents (q.enqueue value) = contents q ++ [value] := by
  simp [Std.Queue.enqueue, contents, List.append_assoc]

/-- **The queue emptiness test matches the contents.** For every queue $q$, the emptiness test
of $q$ returns true if and only if the contents of $q$ are empty. -/
@[simp]
theorem isEmpty_eq_true_iff (q : Std.Queue α) :
    q.isEmpty = true ↔ contents q = [] := by
  cases q with
  | mk eList dList => simp [Std.Queue.isEmpty, contents, Bool.and_eq_true, List.isEmpty_iff]

/-- **Dequeueing fails exactly on empty queues.** For every queue $q$, dequeueing $q$ returns
nothing if and only if the contents of $q$ are empty. -/
@[simp]
theorem dequeue?_eq_none_iff (q : Std.Queue α) :
    q.dequeue? = none ↔ contents q = [] := by
  cases q with
  | mk eList dList =>
      cases dList with
      | cons head tail => simp [Std.Queue.dequeue?, contents]
      | nil =>
          cases eList with
          | nil => simp [Std.Queue.dequeue?, contents]
          | cons head tail =>
              cases h : tail.reverse <;> simp [Std.Queue.dequeue?, contents, h]

/-- **A successful dequeue splits off the first element.** If dequeueing a queue $q$ succeeds
and returns an element $a$ and a queue $r$, then the contents of $q$ are $a$ followed by the
contents of $r$. -/
theorem contents_eq_cons_of_dequeue?_eq_some
    {q : Std.Queue α} {head : α} {rest : Std.Queue α}
    (h : q.dequeue? = some (head, rest)) :
    contents q = head :: contents rest := by
  cases q with
  | mk eList dList =>
      cases dList with
      | cons d ds =>
          simp [Std.Queue.dequeue?] at h
          obtain ⟨hhead, hrest⟩ := h
          cases hhead
          cases hrest
          rfl
      | nil =>
          cases hr : eList.reverse with
          | nil => simp [Std.Queue.dequeue?, hr] at h
          | cons d ds =>
              simp [Std.Queue.dequeue?, hr] at h
              obtain ⟨hhead, hrest⟩ := h
              cases hhead
              cases hrest
              simpa [contents] using hr

end Cslib.Algorithms.Lean.Queue
