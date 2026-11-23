/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Sahlqvist

/-!
# Consumer tests for the Sahlqvist syntax classifiers

Polarity tests distinguish an atom, its negation and double negation. Concrete
boxed semantics checks iteration depth. Distinct Boolean atom names satisfy
the outer disjunction's vocabulary condition; a repeated name does not.
-/

set_option autoImplicit false

open Cslib.Modal

namespace CSLibExtTest.Logics.Modal.Sahlqvist

example : IsPositive (.bot : Formula Bool) ∧ IsNegative (.bot : Formula Bool) :=
  ⟨trivial, trivial⟩

example : IsPositive (.atom false : Formula Bool) := trivial

example : ¬ IsNegative (.atom true : Formula Bool) := by
  intro h
  exact h

example : IsNegative ((Formula.atom true).neg) := by
  simp [IsPositive, IsNegative, Formula.neg]

example : ¬ IsPositive ((Formula.atom true).neg) := by
  simp [IsPositive, IsNegative, Formula.neg]

example : IsPositive ((Formula.atom false).neg.neg) := by
  simp [IsPositive, IsNegative, Formula.neg]

example : IsPositive ((Formula.box (.atom false)).and (Formula.dia (.atom true))) := by
  simp [IsPositive, IsNegative, Formula.and, Formula.dia, Formula.neg]

example : IsNegative ((Formula.atom false).neg.and
    (Formula.box ((Formula.atom true).neg))) := by
  simp [IsPositive, IsNegative, Formula.and, Formula.neg]

private def chain : KripkeModel Bool Unit where
  nonempty_world := ⟨false⟩
  rel := fun w v => w = false ∧ v = true
  valuation := fun w _ => w = true

/-- Zero boxes retain the starting world's false atom. -/
example : ¬ chain.Satisfies false (boxPow 0 (.atom ())) := Bool.false_ne_true

/-- One box sees the successor, so boxed falsity fails. -/
example : ¬ chain.Satisfies false (boxPow 1 .bot) := by
  intro h
  exact h true ⟨rfl, rfl⟩

/-- Two boxes see the successor's dead end, so doubly boxed falsity holds. -/
example : chain.Satisfies false (boxPow 2 .bot) := by
  rintro v ⟨_, rfl⟩ u ⟨h, _⟩
  exact (Bool.false_ne_true h.symm).elim

example : IsSahlqvistAntecedent
    (((boxPow 2 (.atom false)).and (Formula.atom true).neg).dia) :=
  .dia _ (.and _ _ (.boxedAtom false 2)
    (.ofNegative _ ⟨trivial, trivial⟩))

example : IsSahlqvistAntecedent
    ((boxPow 0 (.atom true)).or (Formula.atom false).neg) :=
  .or _ _ (.boxedAtom true 0) (.ofNegative _ ⟨trivial, trivial⟩)

example : IsSahlqvistImplication ((Formula.atom false).neg.imp (.atom true)) :=
  ⟨(Formula.atom false).neg, .atom true,
    .ofNegative _ ⟨trivial, trivial⟩, trivial, rfl⟩

example : IsSahlqvist (.box (Formula.axiomB (.atom false))) :=
  .box (isSahlqvist_axiomB false)

example : IsSahlqvist ((Formula.axiomB (.atom false)).and
    (Formula.axiomB (.atom true))) :=
  .and (isSahlqvist_axiomB false) (isSahlqvist_axiomB true)

example : (Formula.axiomB (.atom false)).atoms = {false} := by
  apply Set.ext
  intro a
  simp [Formula.atoms, Formula.axiomB, Formula.dia, Formula.neg]

example : IsSahlqvist ((Formula.axiomB (.atom false)).or
    (Formula.axiomB (.atom true))) :=
  .or (isSahlqvist_axiomB false) (isSahlqvist_axiomB true) (by
    simpa [Formula.atoms, Formula.axiomB, Formula.dia, Formula.neg] using
      (Set.disjoint_singleton.mpr Bool.false_ne_true : Disjoint ({false} : Set Bool) {true}))

/-- This checks the failed side condition, without claiming every overlapping
disjunction is rejected by all possible parses of the derived connectives. -/
example : ¬ Disjoint (Formula.axiomB (.atom false)).atoms
    (Formula.axiomB (.atom false)).atoms := by
  simp [Formula.atoms, Formula.axiomB, Formula.dia, Formula.neg,
    Set.disjoint_singleton]

end CSLibExtTest.Logics.Modal.Sahlqvist
