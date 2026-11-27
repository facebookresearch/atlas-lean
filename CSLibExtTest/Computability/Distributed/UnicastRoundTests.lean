/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Distributed.UnicastRound

/-!
# Tests for unicast rounds

Repeated messages use separate send positions. Two links forming a path in the process graph
need not give a path in the event order, since intermediate processes do not forward receipts.
-/

namespace Cslib.Distributed.UnicastRound.Tests

open LamportClock

private def links : List (Fin 3 × Fin 3) := [(0, 1), (0, 1), (1, 2)]

example : (execution links).map Event.recvFrom =
    [none, none, none, none, none, none, some 3, some 4, some 5, none, none, none] := by decide

example : WellFormed (execution links) ∧ SingleDelivery (execution links) :=
  ⟨wellFormed _, singleDelivery _⟩

example : HappensBefore (execution links) 0 10 :=
  (first_before_last_iff links 0 1).2 (Or.inr (by decide))

example : ¬ HappensBefore (execution links) 0 11 := by
  intro h
  exact (by decide : ¬ ((0 : Fin 3) = 2 ∨ (0, 2) ∈ links)) ((first_before_last_iff links 0 2).1 h)

-- Both receives name an earlier position; counting only well-formedness would admit fan-out.
private def fanout : List (Event (Fin 3)) := [⟨0, none⟩, ⟨1, some 0⟩, ⟨2, some 0⟩]

example : WellFormed fanout ∧ ¬ SingleDelivery fanout := by
  constructor
  · intro j ej i hj hr
    have hj' : j < 3 := (List.getElem?_eq_some_iff.mp hj).1
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjcases with rfl | rfl | rfl <;> simp [fanout] at hj <;> subst ej <;> simp_all
    omega
  · intro h
    have h₁₂ := h (i := 0) (j := 1) (k := 2) rfl rfl rfl rfl
    omega

end Cslib.Distributed.UnicastRound.Tests
