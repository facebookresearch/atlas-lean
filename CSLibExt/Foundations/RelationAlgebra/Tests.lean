/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.RelationAlgebra.Representation

/-!
# Diagonal tests and relational verification

Assertions embed into CSLib's `SquareRelations` as restricted diagonals.
Composition is in execution order and the order is relation inclusion.
Test negation is complement relative to identity, not full relation
complement. Verification inequalities, absorption and absence of bad exits
are characterized using Mathlib's canonical `SetRel.core`.

These project-authored results apply to arbitrary relations and do not
depend on a particular program syntax or a relational Kleene backend.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {World : Type*}

/-- The diagonal relation restricted to an assertion. -/
def testSet (P : Set World) : SquareRelations World :=
  {(s, t) | s = t ∧ s ∈ P}

/-- Membership in a diagonal test. -/
@[simp] theorem mem_testSet {P : Set World} {s t : World} :
    testSet P (s, t) ↔ s = t ∧ s ∈ P := Iff.rfl

/-- A test is a subidentity, not an arbitrary relation. -/
theorem testSet_le_one (P : Set World) : testSet P ≤ 1 :=
  fun _ h => h.1

/-- Sequential tests conjoin their assertions without changing state. -/
@[simp] theorem testSet_mul_testSet (P Q : Set World) :
    testSet P * testSet Q = testSet (P ∩ Q) := by
  change SetRel.comp (testSet P) (testSet Q) = testSet (P ∩ Q)
  apply Set.ext
  rintro ⟨s, t⟩
  constructor
  · rintro ⟨u, ⟨rfl, hP⟩, rfl, hQ⟩
    exact ⟨rfl, hP, hQ⟩
  · rintro ⟨rfl, hP, hQ⟩
    exact ⟨s, ⟨rfl, hP⟩, rfl, hQ⟩

/-- The verification inequality is precisely universal partial
correctness: every execution from `P` ends in `Q`. -/
theorem test_mul_le_mul_test_iff (P Q : Set World)
    (R : SquareRelations World) :
    testSet P * R ≤ R * testSet Q ↔ P ⊆ SetRel.core R Q := by
  constructor
  · intro h s hP t hR
    have hleft : (testSet P * R) (s, t) := ⟨s, ⟨rfl, hP⟩, hR⟩
    obtain ⟨u, hRu, hut, hQ⟩ := h hleft
    subst t
    exact hQ
  · rintro h ⟨s, t⟩ ⟨u, ⟨rfl, hP⟩, hR⟩
    exact ⟨t, hR, rfl, h hP hR⟩

/-- A postcondition can be absorbed on the right exactly when it holds
on every execution starting in the precondition. -/
theorem test_mul_eq_test_mul_test_iff (P Q : Set World)
    (R : SquareRelations World) :
    testSet P * R = testSet P * R * testSet Q ↔
      P ⊆ SetRel.core R Q := by
  constructor
  · intro h s hP t hR
    have hin : (testSet P * R) (s, t) := ⟨s, ⟨rfl, hP⟩, hR⟩
    rw [h] at hin
    obtain ⟨u, _, hut, hQ⟩ := hin
    subst t
    exact hQ
  · intro h
    apply Set.ext
    rintro ⟨s, t⟩
    constructor
    · intro hin
      obtain ⟨u, ⟨rfl, hP⟩, hR⟩ := hin
      exact ⟨t, ⟨s, ⟨rfl, hP⟩, hR⟩, rfl, h hP hR⟩
    · rintro ⟨u, hin, rfl, _⟩
      exact hin

/-- Classically, verification means that no execution from `P` can
reach the complement of `Q`. -/
theorem test_mul_test_compl_eq_bot_iff (P Q : Set World)
    (R : SquareRelations World) :
    testSet P * R * testSet Qᶜ = ⊥ ↔ P ⊆ SetRel.core R Q := by
  classical
  constructor
  · intro h s hP t hR
    by_contra hQ
    have hbad : (testSet P * R * testSet Qᶜ) (s, t) :=
      ⟨t, ⟨s, ⟨rfl, hP⟩, hR⟩, rfl, hQ⟩
    rw [h] at hbad
    exact hbad
  · intro h
    apply Set.ext
    rintro ⟨s, t⟩
    constructor
    · rintro ⟨u, ⟨v, ⟨rfl, hP⟩, hR⟩, rfl, hQ⟩
      exact (hQ (h hP hR)).elim
    · intro hbot
      exact hbot.elim

/-- The false assertion is the zero relation. -/
@[simp] theorem testSet_empty : testSet (∅ : Set World) = ⊥ := by
  apply Set.ext
  rintro ⟨s, t⟩
  exact ⟨fun h => h.2, fun h => h.elim⟩

/-- The true assertion is the identity relation. -/
@[simp] theorem testSet_univ : testSet (Set.univ : Set World) = 1 := by
  apply Set.ext
  rintro ⟨s, t⟩
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- Boolean test negation is complement relative to identity, not the
full relation-algebra complement (which includes off-diagonal pairs). -/
theorem testSet_compl (P : Set World) :
    testSet Pᶜ = (testSet P)ᶜ ⊓ 1 := by
  apply Set.ext
  rintro ⟨s, t⟩
  constructor
  · rintro ⟨rfl, hP⟩
    exact ⟨fun h => hP h.2, rfl⟩
  · rintro ⟨hP, rfl⟩
    exact ⟨rfl, fun h => hP ⟨rfl, h⟩⟩

/-- Union of assertions is union of their diagonal tests. -/
theorem testSet_union (P Q : Set World) :
    testSet (P ∪ Q) = testSet P ⊔ testSet Q := by
  apply Set.ext
  rintro ⟨s, t⟩
  exact and_or_left

end Cslib.RelationAlgebra
