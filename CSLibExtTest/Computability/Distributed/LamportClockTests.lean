/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.LamportClock
public import Mathlib.Order.Fin.Basic

/-!
# Tests for Lamport clocks

An execution of two processes: `p0` has an internal event and then sends a
message, `p1` has an internal event and then receives that message, and `p0`
has another internal event.

* The timestamps are `1, 2, 1, 3, 3`.
* Sending and receiving, and a chain through process order and a message, are
  instances of happened-before, and the clock condition orders their
  timestamps.
* The converse fails: the internal event of `p1` gets a smaller timestamp than
  the send of `p0`, although neither happened before the other.
* The execution is well formed; a receipt naming a later event is not.
* Lamport's total order follows happened-before and breaks the tie between
  the concurrent events `3` and `4`, which share a timestamp, by process.
-/

@[expose] public section

namespace Cslib.Distributed.LamportClock.Tests

/-- The example execution. -/
def tr : List (Event (Fin 2)) :=
  [⟨0, none⟩, ⟨0, none⟩, ⟨1, none⟩, ⟨1, some 1⟩, ⟨0, none⟩]

example : timestamps tr = [1, 2, 1, 3, 3] := by decide

/-- The message from event `1` to event `3`. -/
theorem hb13 : HappensBefore tr 1 3 :=
  .single ⟨by decide, _, _, rfl, rfl, Or.inr rfl⟩

/-- Event `0` happened before event `3`: process order, then the message. -/
theorem hb03 : HappensBefore tr 0 3 :=
  .tail (.single ⟨by decide, _, _, rfl, rfl, Or.inl rfl⟩) ⟨by decide, _, _, rfl, rfl, Or.inr rfl⟩

example : (timestamps tr).getD 0 0 < (timestamps tr).getD 3 0 := clock_condition hb03

/-- The converse of the clock condition fails: event `2` has the smaller
timestamp, but did not happen before event `1`. -/
example : (timestamps tr).getD 2 0 < (timestamps tr).getD 1 0 ∧ ¬ HappensBefore tr 2 1 :=
  ⟨by decide, fun h => absurd h.lt (by decide)⟩

example : WellFormed tr := by
  intro j ej i hj hr
  rcases j with _ | _ | _ | _ | _ | j <;> simp only [tr] at hj <;>
    first
    | (simp at hj; done)
    | (obtain rfl := Option.some.inj hj; simp at hr; done)
    | (obtain rfl := Option.some.inj hj; simp at hr; omega)

/-- A receipt naming a later event is not well formed; it is no message edge,
and its message lookup contributes `0`. -/
example : ¬ WellFormed [(⟨1, some 1⟩ : Event (Fin 2)), ⟨0, none⟩] := fun h =>
  absurd (h 0 _ 1 rfl rfl) (by decide)

example : timestamps [(⟨1, some 1⟩ : Event (Fin 2)), ⟨0, none⟩] = [1, 1] := by decide

/-- Concurrent events may even share a timestamp. -/
example : (timestamps tr).getD 3 0 = (timestamps tr).getD 4 0 := by decide

/-- Lamport's total order follows happened-before. -/
example : TotalBefore tr 0 3 := totalBefore_of_happensBefore hb03

/-- Concurrent events with equal timestamps are ordered by process: event `4`
of `p0` comes before event `3` of `p1`, although it is later in the list. -/
example : TotalBefore tr 4 3 := ⟨_, _, rfl, rfl, by decide⟩

example : ¬ TotalBefore tr 3 4 := fun h =>
  totalBefore_irrefl tr 3 (totalBefore_trans h ⟨_, _, rfl, rfl, by decide⟩)

end Cslib.Distributed.LamportClock.Tests
