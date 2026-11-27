/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Distributed.CausalClockDimension

/-!
# Tests for the dimension bound

The two-process witness contains exactly two disjoint two-event chains. On three processes
one strict vector comparison has an unchanged coordinate, while a missing comparison is a
strict increase of the ordinary Lamport scalar. The clock computations below do not use the
crown's marker comparison theorem.
-/

namespace Cslib.Distributed.CausalClockDimension.Tests

open LamportClock

example : (crown 2).map (fun e => (e.proc, e.recvFrom)) =
    [(0, none), (1, none), (0, none), (1, none)] := by decide

example (a b : Fin 4) : HappensBefore (crown 2) a b ↔
    (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 3) := by
  rw [VectorClock.happensBefore_iff_lt (by exact a.isLt) (by exact b.isLt), Pi.lt_def]
  revert a b
  decide

example {α : Type*} [LinearOrder α] : ¬ ∃ t : Fin (crown 2).length → α,
    ∀ a b : Fin (crown 2).length, HappensBefore (crown 2) a b ↔ t a < t b :=
  no_scalar_clock (by decide)

example : crownLinks 3 = [(0, 2), (1, 0), (2, 1)] := by decide

example : (crown 3).map Event.recvFrom =
    [none, none, none, none, none, none, some 3, some 4, some 5, none, none, none] := by decide

private def v (a : ℕ) := (VectorClock.timestamps (crown 3)).getD a 0

-- Nonlocal positive: event 0 reaches 11 via 3 → 6, but coordinate 1 stays zero.
example : HappensBefore (crown 3) 0 11 ∧ v 0 1 = v 11 1 := by
  refine ⟨(VectorClock.happensBefore_iff_lt (by decide) (by decide)).2 ?_, by decide⟩
  exact Pi.lt_def.mpr ⟨by decide, 0, by decide⟩

-- The cyclically omitted pair: the scalar orders 0 before 10, the vectors are incomparable.
example : (timestamps (crown 3)).getD 0 0 < (timestamps (crown 3)).getD 10 0 ∧
    ¬ HappensBefore (crown 3) 0 10 ∧ ¬ HappensBefore (crown 3) 10 0 := by
  refine ⟨by decide, fun h => ?_, fun h => ?_⟩
  · exact absurd ((VectorClock.vectorClock_le_of_happensBefore h) 0) (by decide)
  · exact absurd ((VectorClock.vectorClock_le_of_happensBefore h) 1) (by decide)

example {α : Type*} [LinearOrder α] (t : Fin (crown 3).length → Fin 2 → α) :
    ¬ ∀ a b : Fin (crown 3).length, HappensBefore (crown 3) a b ↔ t a < t b := by
  intro h
  exact absurd (dimension_le (by decide) t h) (by decide)

-- One process is outside the lower bound's hypotheses: literal positions are an exact scalar.
example (a b : Fin (crown 1).length) : HappensBefore (crown 1) a b ↔ a.val < b.val := by
  constructor
  · exact HappensBefore.lt
  · intro hab
    exact .single ⟨hab, _, _, List.getElem?_eq_getElem a.isLt, List.getElem?_eq_getElem b.isLt,
      Or.inl (Subsingleton.elim _ _)⟩

end Cslib.Distributed.CausalClockDimension.Tests
