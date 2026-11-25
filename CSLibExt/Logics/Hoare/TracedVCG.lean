/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Logics.Hoare.Traced

/-!
# Verification conditions for annotated traced diagrams

Annotations supply the intermediate assertions for sequencing, the four wire
assertions for tensor, and the invariant and body boundary assertions for
feedback. They contain no proofs. Their diagram index fixes the underlying
program, so annotations cannot replace a composite by an atomic specification.

`Annotation.vc` recursively generates local atomic specifications and monoidal
comparison obligations. Satisfying these conditions gives a Hoare derivation.
Conversely, every derivable triple admits a successful annotation, including
derivations using consequence. With a trace-preserving verification functor this
also characterizes semantic validity.

This is verification-condition generation with supplied assertions, not invariant
inference or a decision procedure. It requires only preorders and the explicit
monoidal comparisons; no weakest-precondition or strict-monoidal assumption is used.

The local conditions follow Arthan, Martin, Mathiesen and Oliva,
*A General Framework for Sound and Complete Floyd-Hoare Logics*, Figure 6,
https://arxiv.org/abs/0807.1016. Assertion annotations and verification-condition
generation follow the method of Nipkow and Klein, *Concrete Semantics*, Section 12.4.
-/

@[expose] public section
namespace Cslib.TracedHoare
open CategoryTheory MonoidalCategory CategoryTheory.VerificationFunctor
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonoidalCategory
universe u v w a
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {Atom : C → C → Type a} (F : C ⥤ MonRelCat.{w}) [F.Monoidal]

/-- Proof-free assertion annotations of a fixed typed diagram. -/
inductive Annotation : {X Y : C} → Diagram Atom X Y → Type (max u w a)
  | atom {X Y} (block : Atom X Y) : Annotation (.atom block)
  | seq {X Y Z} {first : Diagram Atom X Y} {second : Diagram Atom Y Z}
      (middle : F.obj Y) (left : Annotation first) (right : Annotation second) :
      Annotation (.seq first second)
  | tensor {X Y U V} {left : Diagram Atom X Y} {right : Diagram Atom U V}
      (p : F.obj X) (u : F.obj U) (q : F.obj Y) (v : F.obj V)
      (leftAnn : Annotation left) (rightAnn : Annotation right) : Annotation (.tensor left right)
  | feedback {X Y U} {body : Diagram Atom (X ⊗ U) (Y ⊗ U)}
      (invariant : F.obj U) (input : F.obj (X ⊗ U)) (output : F.obj (Y ⊗ U))
      (bodyAnn : Annotation body) : Annotation (.feedback body)

variable {F} (interpret : ∀ {X Y}, Atom X Y → (X ⟶ Y))

/-- Generate local obligations; only atomic blocks are interpreted semantically. -/
def Annotation.vc : {X Y : C} → {d : Diagram Atom X Y} →
    Annotation F d → F.obj X → F.obj Y → Prop
  | _, _, _, .atom block, P, Q => Triple F (interpret block) P Q
  | _, _, _, .seq R first second, P, Q => first.vc P R ∧ second.vc R Q
  | _, _, _, .tensor (X := X₁) (Y := Y₁) (U := X₂) (V := Y₂) p u q v left right, P, Q =>
      (P, (p, u)) ∈ (δ F X₁ X₂).rel ∧ left.vc p q ∧ right.vc u v ∧
        ((q, v), Q) ∈ (μ F Y₁ Y₂).rel
  | _, _, _, .feedback (X := X) (Y := Y) (U := U) I P' Q' body, P, Q =>
      ((P, I), P') ∈ (μ F X U).rel ∧ body.vc P' Q' ∧ (Q', (Q, I)) ∈ (δ F Y U).rel

variable {interpret}

/-- Strengthening the input and weakening the output preserves the same annotation. -/
theorem Annotation.vc_consequence {X Y} {d : Diagram Atom X Y} (A : Annotation F d)
    {P P' : F.obj X} {Q Q' : F.obj Y} (h : A.vc interpret P Q)
    (hP : P' ≤ P) (hQ : Q ≤ Q') : A.vc interpret P' Q' := by
  induction A with
  | atom block => exact h.consequence F hP hQ
  | seq R first second ihFirst ihSecond =>
      exact ⟨ihFirst h.1 hP le_rfl, ihSecond h.2 le_rfl hQ⟩
  | tensor p u q v left right _ _ =>
      exact ⟨(δ F _ _).closed hP le_rfl h.1, h.2.1, h.2.2.1,
        (μ F _ _).closed le_rfl hQ h.2.2.2⟩
  | feedback I input output body _ =>
      exact ⟨(μ F _ _).closed (x := (P, I)) (x' := (P', I)) ⟨hP, le_rfl⟩ le_rfl h.1,
        h.2.1, (δ F _ _).closed (y := (Q, I)) (y' := (Q', I)) le_rfl ⟨hQ, le_rfl⟩ h.2.2⟩

/-- Successful local obligations construct a Hoare derivation of the indexed diagram. -/
theorem Annotation.vc_sound {X Y} {d : Diagram Atom X Y} (A : Annotation F d)
    {P : F.obj X} {Q : F.obj Y} (h : A.vc interpret P Q) :
    Derivable interpret F P d Q := by
  induction A with
  | atom block => exact .atom block h
  | seq R first second ihFirst ihSecond => exact .seq (ihFirst h.1) (ihSecond h.2)
  | tensor p u q v left right ihLeft ihRight =>
      exact .tensor h.1 (ihLeft h.2.1) (ihRight h.2.2.1) h.2.2.2
  | feedback I P' Q' body ih => exact .feedback I h.1 (ih h.2.1) h.2.2

/-- Every derivation admits annotations satisfying the local conditions. -/
theorem Derivable.exists_annotation {X Y} {d : Diagram Atom X Y}
    {P : F.obj X} {Q : F.obj Y} (h : Derivable interpret F P d Q) :
    ∃ A : Annotation F d, A.vc interpret P Q := by
  induction h with
  | atom block h => exact ⟨.atom block, h⟩
  | consequence _ hP hQ ih =>
      obtain ⟨A, hA⟩ := ih
      exact ⟨A, A.vc_consequence hA hP hQ⟩
  | @seq X Y Z first second P R Q _ _ ihFirst ihSecond =>
      obtain ⟨A, hA⟩ := ihFirst
      obtain ⟨B, hB⟩ := ihSecond
      exact ⟨.seq R A B, hA, hB⟩
  | @tensor X Y U V left right P Q p u q v hP _ _ hQ ihLeft ihRight =>
      obtain ⟨A, hA⟩ := ihLeft
      obtain ⟨B, hB⟩ := ihRight
      exact ⟨.tensor p u q v A B, hP, hA, hB, hQ⟩
  | @feedback X Y U body P Q I P' Q' hP _ hQ ih =>
      obtain ⟨A, hA⟩ := ih
      exact ⟨.feedback I P' Q' A, hP, hA, hQ⟩

/-- Annotation existence characterizes derivability, without a trace-preservation hypothesis. -/
theorem derivable_iff_exists_annotation (interpret : ∀ {X Y}, Atom X Y → (X ⟶ Y))
    (F : C ⥤ MonRelCat.{w}) [F.Monoidal] {X Y} (d : Diagram Atom X Y)
    (P : F.obj X) (Q : F.obj Y) :
    Derivable interpret F P d Q ↔ ∃ A : Annotation F d, A.vc interpret P Q :=
  ⟨Derivable.exists_annotation, fun ⟨A, h⟩ => A.vc_sound h⟩

/-- For trace-preserving verification, successful annotations characterize semantic validity. -/
theorem triple_iff_exists_annotation (interpret : ∀ {X Y}, Atom X Y → (X ⟶ Y))
    [SymmetricCategory C] (T : SymmetricTrace C) (F : C ⥤ MonRelCat.{w}) [F.Monoidal]
    (hF : T.Preserves MonRelCat.symmetricTrace F)
    {X Y} (d : Diagram Atom X Y) (P : F.obj X) (Q : F.obj Y) :
    Triple F (d.denote interpret T) P Q ↔ ∃ A : Annotation F d, A.vc interpret P Q :=
  (derivable_iff_triple interpret T F hF d P Q).symm.trans
    (derivable_iff_exists_annotation interpret F d P Q)

end Cslib.TracedHoare
