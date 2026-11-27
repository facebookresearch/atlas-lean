/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Foundations.Semantics.PlaceTransitionNet
import Mathlib.Data.Fintype.Fin

/-!
# Tests for weighted place/transition Petri nets

Murata, *Proceedings of the IEEE* 77(4), 1989, §II, Fig. 1 (p. 543), gives
an abstract three-place test: the marking `(2,2,0)` becomes `(0,1,2)`, then
the transition is disabled. A separate loop has positive net gain but still
requires two tokens before it can fire. The other examples distinguish
transition identities, test source, sink and isolated transitions, and allow
either the place type or the transition type to be empty, but not both.
-/

namespace Cslib.PlaceTransitionNetTest

private def figureOne : MarkedPlaceTransitionNet (Fin 3) Unit where
  nonempty := ⟨.inr ()⟩
  input p _ := if p = 0 then 2 else if p = 1 then 1 else 0
  output _ p := if p = 2 then 2 else 0
  initial p := if p = 2 then 0 else 2

private abbrev fig := figureOne.toPlaceTransitionNet

example : (fig.fire? figureOne.initial ()).map (fun m => (m 0, m 1, m 2)) =
    some (0, 1, 2) := by decide

example : fig.run? figureOne.initial [(), ()] = none := rfl

-- Satisfying the first input does not compensate for a shortage at the second.
example : fig.fire? (fun p => if p = 0 then 5 else 0) () = none := rfl

example : Sum.inl 0 ∈ fig.preset (.inr ()) ∧ Sum.inl 2 ∉ fig.preset (.inr ()) ∧
    Sum.inl 2 ∈ fig.postset (.inr ()) ∧ Sum.inr () ∈ fig.preset (.inl 2) ∧
    Sum.inr () ∈ fig.postset (.inl 1) ∧ Sum.inr () ∉ fig.postset (.inl 2) ∧
    fig.weight (.inl 0) (.inl 1) = 0 ∧ fig.weight (.inr ()) (.inr ()) = 0 := by
  change (0 < 2 ∧ ¬0 < 0 ∧ 0 < 2 ∧ 0 < 2 ∧ 0 < 1 ∧ ¬0 < 0 ∧ 0 = 0 ∧ 0 = 0)
  decide

private def loop : PlaceTransitionNet Unit Unit where
  nonempty := ⟨.inl ()⟩
  input _ _ := 2
  output _ _ := 3

private abbrev count (n : ℕ) : PlaceTransitionNet.Marking Unit := fun _ => n

example : ¬loop.IsOrdinary := fun h => by
  have := h (.inl ()) (.inr ()) (by decide : 0 < 2)
  exact (by decide : ¬2 = 1) this

example : loop.fire? (count 1) () = none := rfl
example : ¬loop.toLTS.Tr (count 1) () (count 2) := fun h => Nat.not_succ_le_self 1 (h.1 ())
example : loop.fire? (count 2) () = some (count 3) := rfl
example : loop.run? (count 2) [(), ()] = some (count 4) := rfl
example : loop.toLTS.MTr (count 2) [(), ()] (count 4) := (loop.run?_eq_some_iff ..).mp rfl
example : loop.run? (count 1) [] = some (count 1) := rfl

example {m : PlaceTransitionNet.Marking Unit} (h : loop.toLTS.MTr (count 2) [(), ()] m) :
    m = count 4 :=
  LTS.Deterministic.eq_of_mTr h ((loop.run?_eq_some_iff ..).mp rfl)

-- Transition 0 produces one token, 1 consumes one, and 2 has no incident arcs.
private def switches : PlaceTransitionNet Unit (Fin 3) where
  nonempty := ⟨.inl ()⟩
  input _ t := if t = 1 then 1 else 0
  output t _ := if t = 0 then 1 else 0

example : switches.IsOrdinary := by
  intro x y h
  cases x <;> cases y <;> simp_all [PlaceTransitionNet.postset, PlaceTransitionNet.weight, switches]
  all_goals split at h <;> simp_all

example : switches.run? (count 0) [0, 1] = some (count 0) := rfl
example : switches.run? (count 0) [1, 0] = none := rfl
example : switches.fire? (count 7) 2 = some (count 7) := rfl

-- Hiding the transition witness is weaker than prescribing the sink label.
example : switches.toLTS.CanReach (count 0) (count 1) ∧
    ¬switches.toLTS.MTr (count 0) [1] (count 1) := by
  refine ⟨⟨[0], (switches.run?_eq_some_iff ..).mp rfl⟩, ?_⟩
  rw [← switches.run?_eq_some_iff]
  decide

private def placesOnly : PlaceTransitionNet Unit (Fin 0) where
  nonempty := ⟨.inl ()⟩
  input _ := Fin.elim0
  output := Fin.elim0

example (M M' : PlaceTransitionNet.Marking Unit) : placesOnly.toLTS.CanReach M M' ↔ M = M' := by
  constructor
  · rintro ⟨_ | ⟨t, ts⟩, h⟩
    · exact LTS.MTr.nil_eq placesOnly.toLTS h
    · exact t.elim0
  · rintro rfl
    exact LTS.CanReach.refl placesOnly.toLTS M

private def transitionsOnly : PlaceTransitionNet (Fin 0) Unit where
  nonempty := ⟨.inr ()⟩
  input := Fin.elim0
  output _ := Fin.elim0

example (M : PlaceTransitionNet.Marking (Fin 0)) (ts : List Unit) :
    transitionsOnly.run? M ts = some M := by
  apply (transitionsOnly.run?_eq_some_iff ..).mpr
  induction ts with
  | nil => exact .refl
  | cons t ts ih => exact .stepL ⟨fun p => p.elim0, fun p => p.elim0⟩ ih

example : ¬Nonempty (PlaceTransitionNet (Fin 0) (Fin 0)) := by
  rintro ⟨N⟩
  obtain ⟨p | t⟩ := N.nonempty
  · exact p.elim0
  · exact t.elim0

end Cslib.PlaceTransitionNetTest
