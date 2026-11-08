/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.PDL.Basic

/-!
# Consumer tests for propositional dynamic logic

The Boolean action `true` flips a Boolean world, while `false` leaves it alone.
Tests distinguish sequence order, both choice branches, blocked and successful
tests, and zero-step iteration. A three-world chain requires two iterations
to reach a state that a single atomic step cannot reach.
-/

set_option autoImplicit false

open Cslib.PDL

namespace CSLibExtTest.Logics.PDL.Basic

private def twoActions : Model Bool Unit Bool where
  rel := fun a w v => if a then v = !w else v = w
  valuation := fun w _ => w = true

example : ProgRel twoActions (.atomic true) false true := rfl

example : ProgRel twoActions (.atomic false) false false := rfl

example : ¬ ProgRel twoActions (.atomic true) false false := by
  intro h
  exact Bool.false_ne_true h

/-- Flip first, then test heads: the test succeeds in the successor world. -/
example : ProgRel twoActions (.seq (.atomic true) (.test (.atom ()))) false true :=
  ⟨true, rfl, ⟨rfl, rfl⟩⟩

/-- Reversing the sequence blocks at the initial tails world. -/
example : ¬ ProgRel twoActions (.seq (.test (.atom ())) (.atomic true)) false true := by
  rintro ⟨u, ⟨_, h⟩, _⟩
  exact Bool.false_ne_true h

example : ProgRel twoActions (.choice (.atomic true) (.atomic false)) false true :=
  Or.inl rfl

example : ProgRel twoActions (.choice (.atomic true) (.atomic false)) false false :=
  Or.inr rfl

example : ProgRel twoActions (.test (.atom ())) true true := ⟨rfl, rfl⟩

example : ¬ ProgRel twoActions (.test (.atom ())) false false := by
  intro h
  exact Bool.false_ne_true h.2

/-- A successful test keeps the world unchanged. -/
example : ¬ ProgRel twoActions (.test (.atom ())) true false := by
  intro h
  exact Bool.false_ne_true h.1.symm

/-- Even an always-blocked program has a zero-step iteration. -/
example : ProgRel twoActions (.star (.test .bot)) false false :=
  Relation.ReflTransGen.refl

private def stepChain : Model (Fin 3) Unit Unit where
  rel := fun _ w v => v.val = w.val + 1
  valuation := fun w _ => w = 2

/-- The endpoint `2` requires two atomic steps from `0`. -/
example : ProgRel stepChain (.star (.atomic ())) 0 2 :=
  Relation.ReflTransGen.head (b := (1 : Fin 3)) rfl
    (Relation.ReflTransGen.single rfl)

example : ¬ ProgRel stepChain (.atomic ()) 0 2 := by
  change (2 : Nat) ≠ 1
  decide

/-- Two executions reach the world where the atom holds. -/
example : Sat stepChain (.box (.seq (.atomic ()) (.atomic ())) (.atom ())) 0 := by
  rintro v ⟨u, h0, h1⟩
  have hu : u = (1 : Fin 3) := Fin.ext h0
  subst hu
  exact Fin.ext h1

/-- A single execution stops at `1`, where that atom is false. -/
example : ¬ Sat stepChain (.box (.atomic ()) (.atom ())) 0 := by
  intro h
  exact (by decide : (1 : Fin 3) ≠ 2) (h 1 rfl)

example : Sat twoActions (.box (.atomic true) (.atom ())) false := by
  intro v hv
  exact hv

example : ¬ Sat twoActions (.box (.atomic true) (.atom ())) true := by
  intro h
  exact Bool.false_ne_true (h false rfl)

/-- The sequencing law yields the false atom after two flips. -/
example : ¬ Sat twoActions (.box (.seq (.atomic true) (.atomic true)) (.atom ())) false := by
  intro h
  have hNested := (sat_box_seq twoActions).mp h
  exact Bool.false_ne_true (hNested true rfl false rfl)

/-- Sequencing a blocked test with a flip gives no execution to refute the box. -/
example : Sat twoActions (.box (.seq (.test (.atom ())) (.atomic true)) .bot) false := by
  rw [sat_box_seq twoActions, sat_box_test twoActions]
  intro h
  exact (Bool.false_ne_true h).elim

/-- The choice law must retain the identity branch, where the atom is false. -/
example : ¬ Sat twoActions (.box (.choice (.atomic true) (.atomic false)) (.atom ()))
    false := by
  intro h
  have hIdentity := ((sat_box_choice twoActions).mp h).2
  exact Bool.false_ne_true (hIdentity false rfl)

/-- Star unfolding retains its exit case at the starting world. -/
example : ¬ Sat twoActions (.box (.star (.atomic true)) (.atom ())) false := by
  intro h
  exact Bool.false_ne_true ((sat_box_star_unfold twoActions).mp h).1

example : Sat twoActions (.box (.test (.atom ())) .bot) false := by
  rw [sat_box_test twoActions]
  exact Bool.false_ne_true

example : ¬ Sat twoActions (.box (.test (.atom ())) .bot) true := by
  intro h
  exact (sat_box_test twoActions).mp h rfl

/-- Possibility has a real flipping witness. -/
example : Sat twoActions (.dia (.atomic true) (.atom ())) false := by
  intro h
  exact h true rfl rfl

/-- Possibility fails for a blocked test even when the postcondition is true. -/
example : ¬ Sat twoActions (.dia (.test .bot) (.atom ())) true := by
  intro h
  apply h
  intro v hTest
  exact hTest.2.elim

end CSLibExtTest.Logics.PDL.Basic
