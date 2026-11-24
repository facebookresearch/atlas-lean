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
* Happened-before is a strict order; the position in the list is a clock satisfying C1 and C2;
  the list order and Lamport's own order, two total orders extending happened-before that
  disagree on the events `3` and `4`, each come from a clock system.
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

/-! ### Happened-before as a strict order, and clock systems -/

example : ¬ HappensBefore tr 3 3 := happensBefore_irrefl tr 3

example : IsStrictOrder ℕ (HappensBefore tr) := isStrictOrder_happensBefore tr

/-- The position in the list is a clock satisfying C1 and C2, hence the clock condition. -/
example : (0 : ℕ) < 3 :=
  clockCondition_of_c1_c2 (tr := tr) id (fun _ _ _ _ h _ _ _ => h) (fun _ _ _ h _ _ => h) hb03

/-- The list order is a total order extending happened-before; the clock it yields orders the
concurrent events `3` and `4` the other way round from `TotalBefore`. -/
example : ∃ C : ℕ → ℕ, (∀ a b, HappensBefore tr a b → C a < C b) ∧ ClockBefore tr C 3 4 := by
  obtain ⟨C, hC, hiff⟩ := exists_clock_of_extends (tr := tr) (· < ·) (fun a => lt_irrefl a)
    (fun _ _ _ => lt_trans) (fun a b _ _ hab => lt_or_gt_of_ne hab) (fun _ _ h => h.lt)
  exact ⟨C, hC, (hiff 3 4).mpr ⟨by decide, by decide, by decide⟩⟩

/-- Lamport's own order `TotalBefore` is a strict total order extending happened-before, so it
also comes from a clock system. -/
example : ∃ C : ℕ → ℕ, ∀ a b, ClockBefore tr C a b ↔
    a < tr.length ∧ b < tr.length ∧ TotalBefore tr a b := by
  obtain ⟨C, -, hiff⟩ := exists_clock_of_extends (tr := tr) (TotalBefore tr)
    (totalBefore_irrefl tr) (fun _ _ _ => totalBefore_trans)
    (fun a b ha hb hab => totalBefore_total (List.getElem?_eq_getElem ha)
      (List.getElem?_eq_getElem hb) hab)
    (fun _ _ h => totalBefore_of_happensBefore h)
  exact ⟨C, hiff⟩

/-- Any clock satisfying the clock condition, here the position in the list, induces a strict
total order extending happened-before. -/
example : ClockBefore tr id 0 3 ∧ (ClockBefore tr id 3 4 ∨ ClockBefore tr id 4 3) ∧
    ¬ ClockBefore tr id 2 2 :=
  ⟨clockBefore_of_happensBefore (fun _ _ h => h.lt) hb03,
    clockBefore_total (fun _ _ h => h.lt) rfl rfl (by decide), clockBefore_irrefl tr id 2⟩

end Cslib.Distributed.LamportClock.Tests
