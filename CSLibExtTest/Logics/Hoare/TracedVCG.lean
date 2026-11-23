/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import CSLibExt.Logics.Hoare.TracedVCG

/-! # Generic annotation APIs and successful/failed local obligations -/

open CategoryTheory Cslib.TracedHoare
open scoped MonoidalCategory
universe u v w a
section Generic
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {Atom : C → C → Type a} (interpret : ∀ {X Y}, Atom X Y → (X ⟶ Y))
  (F : C ⥤ MonRelCat.{w}) [F.Monoidal]

example {X Y} (d : Diagram Atom X Y) (P : F.obj X) (Q : F.obj Y) :
    Derivable interpret F P d Q ↔ ∃ A : Annotation F d, A.vc interpret P Q :=
  derivable_iff_exists_annotation interpret F d P Q

example {X Y} {d : Diagram Atom X Y} (A : Annotation F d)
    {P P' : F.obj X} {Q Q' : F.obj Y} (h : A.vc interpret P Q)
    (hP : P' ≤ P) (hQ : Q ≤ Q') : A.vc interpret P' Q' := A.vc_consequence h hP hQ

example {X Y} {d : Diagram Atom X Y} (A : Annotation F d)
    {P : F.obj X} {Q : F.obj Y} (h : A.vc interpret P Q) :
    Derivable interpret F P d Q := A.vc_sound h

example [SymmetricCategory C] (T : SymmetricTrace C)
    (hF : T.Preserves MonRelCat.symmetricTrace F) {X Y} (d : Diagram Atom X Y)
    (P : F.obj X) (Q : F.obj Y) :
    VerificationFunctor.Triple F (d.denote interpret T) P Q ↔
      ∃ A : Annotation F d, A.vc interpret P Q :=
  triple_iff_exists_annotation interpret T F hF d P Q
end Generic

namespace Cslib.TracedHoare.VCGTests
private abbrev N := MonRelCat.of ℕ
private abbrev E := MonRelCat.of Empty

private inductive Blocks : MonRelCat → MonRelCat → Type
  | tick : Blocks N N
  | pass : Blocks (N ⊗ N) (N ⊗ N)
  | empty : Blocks (N ⊗ E) (N ⊗ E)

private noncomputable def interpret : ∀ {X Y}, Blocks X Y → (X ⟶ Y)
  | _, _, .tick => MonRelCat.graph ⟨Nat.succ, fun _ _ h => Nat.succ_le_succ h⟩
  | _, _, .pass => 𝟙 _
  | _, _, .empty => 𝟙 _

private abbrev tick : Diagram Blocks N N := .atom .tick
private abbrev tickAnn : Annotation (𝟭 MonRelCat.{0}) tick := .atom Blocks.tick
private abbrev twice (middle : ℕ) : Annotation (𝟭 MonRelCat.{0}) (.seq tick tick) :=
  .seq middle tickAnn tickAnn

example : tickAnn.vc interpret (0 : ℕ) (1 : ℕ) := by
  change (1 : ℕ) ≤ (1 : ℕ)
  decide
example : ¬ tickAnn.vc interpret (0 : ℕ) (0 : ℕ) := by
  change ¬ (1 : ℕ) ≤ (0 : ℕ)
  decide

example : (twice (1 : ℕ)).vc interpret (0 : ℕ) (2 : ℕ) := by
  change (1 : ℕ) ≤ (1 : ℕ) ∧ (2 : ℕ) ≤ (2 : ℕ)
  decide
example : ¬ (twice (0 : ℕ)).vc interpret (0 : ℕ) (2 : ℕ) := by
  change ¬ ((1 : ℕ) ≤ (0 : ℕ) ∧ (1 : ℕ) ≤ (2 : ℕ))
  decide
example : ¬ (twice (2 : ℕ)).vc interpret (0 : ℕ) (2 : ℕ) := by
  change ¬ ((1 : ℕ) ≤ (2 : ℕ) ∧ (3 : ℕ) ≤ (2 : ℕ))
  decide

example : Derivable interpret (𝟭 MonRelCat.{0}) (X := N) (Y := N) (0 : ℕ) (.seq tick tick) (2 : ℕ) :=
  (twice 1).vc_sound (by change (1 : ℕ) ≤ (1 : ℕ) ∧ (2 : ℕ) ≤ (2 : ℕ); decide)

-- Consequence reuses the same annotation; no extra proof node is required.
example : (twice (2 : ℕ)).vc interpret (0 : ℕ) (4 : ℕ) := by
  apply (twice (2 : ℕ)).vc_consequence (P := (1 : ℕ)) (Q := (3 : ℕ))
  · change (2 : ℕ) ≤ (2 : ℕ) ∧ (3 : ℕ) ≤ (3 : ℕ)
    decide
  · change (0 : ℕ) ≤ (1 : ℕ)
    decide
  · change (3 : ℕ) ≤ (4 : ℕ)
    decide

private abbrev tensorAnn : Annotation (𝟭 MonRelCat.{0}) (.tensor tick tick) :=
  .tensor (0 : ℕ) (3 : ℕ) (1 : ℕ) (4 : ℕ) tickAnn tickAnn

example : tensorAnn.vc interpret ((0 : ℕ), (3 : ℕ)) ((1 : ℕ), (4 : ℕ)) := by
  change ((0 : ℕ) ≤ (0 : ℕ) ∧ (3 : ℕ) ≤ (3 : ℕ)) ∧ (1 : ℕ) ≤ (1 : ℕ) ∧ (4 : ℕ) ≤ (4 : ℕ) ∧ ((1 : ℕ) ≤ (1 : ℕ) ∧ (4 : ℕ) ≤ (4 : ℕ))
  decide

-- The comparison obligations check both the input and output wires.
example : ¬ tensorAnn.vc interpret ((1 : ℕ), (3 : ℕ)) ((1 : ℕ), (4 : ℕ)) := by
  change ¬ (((1 : ℕ) ≤ (0 : ℕ) ∧ (3 : ℕ) ≤ (3 : ℕ)) ∧ (1 : ℕ) ≤ (1 : ℕ) ∧ (4 : ℕ) ≤ (4 : ℕ) ∧ ((1 : ℕ) ≤ (1 : ℕ) ∧ (4 : ℕ) ≤ (4 : ℕ)))
  decide

example : ¬ tensorAnn.vc interpret ((0 : ℕ), (3 : ℕ)) ((1 : ℕ), (3 : ℕ)) := by
  change ¬ (((0 : ℕ) ≤ (0 : ℕ) ∧ (3 : ℕ) ≤ (3 : ℕ)) ∧ (1 : ℕ) ≤ (1 : ℕ) ∧ (4 : ℕ) ≤ (4 : ℕ) ∧ ((1 : ℕ) ≤ (1 : ℕ) ∧ (4 : ℕ) ≤ (3 : ℕ)))
  decide

private abbrev loopAnn (I input output : ℕ) :
    Annotation (𝟭 MonRelCat.{0}) (Diagram.feedback (X := N) (Y := N) (U := N) (.atom Blocks.pass)) :=
  .feedback I ((0 : ℕ), input) ((0 : ℕ), output) (.atom Blocks.pass)

example : (loopAnn (7 : ℕ) (7 : ℕ) (7 : ℕ)).vc interpret (0 : ℕ) (0 : ℕ) := by
  change ((0 : ℕ) ≤ (0 : ℕ) ∧ (7 : ℕ) ≤ (7 : ℕ)) ∧ ((0 : ℕ) ≤ (0 : ℕ) ∧ (7 : ℕ) ≤ (7 : ℕ)) ∧ ((0 : ℕ) ≤ (0 : ℕ) ∧ (7 : ℕ) ≤ (7 : ℕ))
  decide

-- The invariant must enter the body, be preserved, and return to the same hidden assertion.
example : ¬ (loopAnn (7 : ℕ) (6 : ℕ) (7 : ℕ)).vc interpret (0 : ℕ) (0 : ℕ) := by
  change ¬ (((0 : ℕ) ≤ (0 : ℕ) ∧ (7 : ℕ) ≤ (6 : ℕ)) ∧ ((0 : ℕ) ≤ (0 : ℕ) ∧ (6 : ℕ) ≤ (7 : ℕ)) ∧ ((0 : ℕ) ≤ (0 : ℕ) ∧ (7 : ℕ) ≤ (7 : ℕ)))
  decide

example : ¬ (loopAnn (7 : ℕ) (7 : ℕ) (6 : ℕ)).vc interpret (0 : ℕ) (0 : ℕ) := by
  change ¬ (((0 : ℕ) ≤ (0 : ℕ) ∧ (7 : ℕ) ≤ (7 : ℕ)) ∧ ((0 : ℕ) ≤ (0 : ℕ) ∧ (7 : ℕ) ≤ (6 : ℕ)) ∧ ((0 : ℕ) ≤ (0 : ℕ) ∧ (6 : ℕ) ≤ (7 : ℕ)))
  decide

example : ¬ (loopAnn (7 : ℕ) (7 : ℕ) (8 : ℕ)).vc interpret (0 : ℕ) (0 : ℕ) := by
  change ¬ (((0 : ℕ) ≤ (0 : ℕ) ∧ (7 : ℕ) ≤ (7 : ℕ)) ∧ ((0 : ℕ) ≤ (0 : ℕ) ∧ (7 : ℕ) ≤ (8 : ℕ)) ∧ ((0 : ℕ) ≤ (0 : ℕ) ∧ (8 : ℕ) ≤ (7 : ℕ)))
  decide

example : VerificationFunctor.Triple (𝟭 MonRelCat.{0})
    ((Diagram.feedback (X := N) (Y := N) (U := N) (.atom Blocks.pass)).denote interpret MonRelCat.symmetricTrace) (0 : ℕ) (0 : ℕ) :=
  ((loopAnn (7 : ℕ) (7 : ℕ) (7 : ℕ)).vc_sound (by
    change ((0 : ℕ) ≤ (0 : ℕ) ∧ (7 : ℕ) ≤ (7 : ℕ)) ∧ ((0 : ℕ) ≤ (0 : ℕ) ∧ (7 : ℕ) ≤ (7 : ℕ)) ∧ ((0 : ℕ) ≤ (0 : ℕ) ∧ (7 : ℕ) ≤ (7 : ℕ))
    decide)).sound (SymmetricTrace.preserves_id _)

example : ¬ ∃ A : Annotation (𝟭 MonRelCat.{0}) (Diagram.feedback (X := N) (Y := N) (U := E) (.atom Blocks.empty)), A.vc interpret (0 : ℕ) (0 : ℕ) := by
  rintro ⟨A, hA⟩
  have h := (A.vc_sound hA).sound (SymmetricTrace.preserves_id MonRelCat.symmetricTrace)
  obtain ⟨I, _⟩ := (VerificationFunctor.triple_trace_iff (𝟭 MonRelCat)
    (SymmetricTrace.preserves_id MonRelCat.symmetricTrace) _ _ _).mp h
  exact I.elim

example : ∃ A : Annotation (𝟭 MonRelCat.{0}) (.seq tick tick), A.vc interpret (0 : ℕ) (3 : ℕ) := by
  apply Derivable.exists_annotation
  exact (twice 1).vc_sound (by change (1 : ℕ) ≤ (1 : ℕ) ∧ (2 : ℕ) ≤ (3 : ℕ); decide)

#print axioms Annotation.vc_sound
#print axioms Derivable.exists_annotation
#print axioms triple_iff_exists_annotation
end Cslib.TracedHoare.VCGTests
