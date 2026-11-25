/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.VerificationFunctor

/-!
# Hoare logic for typed traced diagrams

Basic blocks have a supplied interpretation in a symmetric traced category.
Diagrams are built from these blocks by sequencing, tensor and feedback.
The Hoare system has semantic axioms only for basic blocks, together with
consequence and a rule for each diagram constructor. It is sound and relatively
complete for every trace-preserving strong monoidal verification functor into
preorders and monotone relations.

Completeness is relative to the validity oracle for basic blocks and semantic
assertion entailment. It neither decides those premises nor proves expressiveness
of a syntactic assertion language. The monoidal comparison relations are explicit,
so no strictness or antisymmetry assumption is hidden in the tensor/feedback rules.

Source: Arthan, Martin, Mathiesen and Oliva, *A General Framework for Sound and
Complete Floyd-Hoare Logics*, Figure 6 and Theorem 3.4,
https://arxiv.org/abs/0807.1016.
-/

@[expose] public section
namespace Cslib.TracedHoare
open CategoryTheory MonoidalCategory CategoryTheory.VerificationFunctor
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonoidalCategory
universe u v w a
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Typed block diagrams; only the supplied family can occur as a basic block. -/
inductive Diagram (Atom : C → C → Type a) : C → C → Type (max u a)
  | atom {X Y} (block : Atom X Y) : Diagram Atom X Y
  | seq {X Y Z} (first : Diagram Atom X Y) (second : Diagram Atom Y Z) : Diagram Atom X Z
  | tensor {X Y U V} (left : Diagram Atom X Y) (right : Diagram Atom U V) :
      Diagram Atom (X ⊗ U) (Y ⊗ V)
  | feedback {X Y U} (body : Diagram Atom (X ⊗ U) (Y ⊗ U)) : Diagram Atom X Y

variable {Atom : C → C → Type a}
  (interpret : ∀ {X Y}, Atom X Y → (X ⟶ Y)) (T : SymmetricTrace C)

/-- Interpret a diagram using categorical composition, tensor and the supplied trace. -/
def Diagram.denote {X Y} : Diagram Atom X Y → (X ⟶ Y)
  | .atom block => interpret block
  | .seq first second => first.denote ≫ second.denote
  | .tensor left right => left.denote ⊗ₘ right.denote
  | .feedback body => T.trace body.denote

variable (F : C ⥤ MonRelCat.{w}) [F.Monoidal]

/-- Derivable Hoare triples. Validity is an axiom premise only at basic blocks. -/
inductive Derivable : {X Y : C} → F.obj X → Diagram Atom X Y → F.obj Y → Prop
  | atom {X Y} (block : Atom X Y) {P : F.obj X} {Q : F.obj Y}
      (h : Triple F (interpret block) P Q) : Derivable P (.atom block) Q
  | consequence {X Y} {d : Diagram Atom X Y} {P P' : F.obj X} {Q Q' : F.obj Y}
      (h : Derivable P d Q) (hP : P' ≤ P) (hQ : Q ≤ Q') : Derivable P' d Q'
  | seq {X Y Z} {first : Diagram Atom X Y} {second : Diagram Atom Y Z}
      {P : F.obj X} {Q : F.obj Y} {R : F.obj Z}
      (hfirst : Derivable P first Q) (hsecond : Derivable Q second R) :
      Derivable P (.seq first second) R
  | tensor {X Y U V} {left : Diagram Atom X Y} {right : Diagram Atom U V}
      {P : F.obj (X ⊗ U)} {Q : F.obj (Y ⊗ V)}
      {p : F.obj X} {u : F.obj U} {q : F.obj Y} {v : F.obj V}
      (hP : (P, (p, u)) ∈ (δ F X U).rel)
      (hleft : Derivable p left q) (hright : Derivable u right v)
      (hQ : ((q, v), Q) ∈ (μ F Y V).rel) : Derivable P (.tensor left right) Q
  | feedback {X Y U} {body : Diagram Atom (X ⊗ U) (Y ⊗ U)}
      {P : F.obj X} {Q : F.obj Y} (I : F.obj U)
      {P' : F.obj (X ⊗ U)} {Q' : F.obj (Y ⊗ U)}
      (hP : ((P, I), P') ∈ (μ F X U).rel) (hbody : Derivable P' body Q')
      (hQ : (Q', (Q, I)) ∈ (δ F Y U).rel) : Derivable P (.feedback body) Q

variable {interpret T F}

/-- Every derivation is valid under a trace-preserving verification functor. -/
theorem Derivable.sound (hF : T.Preserves MonRelCat.symmetricTrace F)
    {X Y} {P : F.obj X} {Q : F.obj Y} {d : Diagram Atom X Y}
    (h : Derivable interpret F P d Q) : Triple F (d.denote interpret T) P Q := by
  induction h with
  | atom block h => exact h
  | consequence _ hP hQ ih => exact ih.consequence F hP hQ
  | seq _ _ ihFirst ihSecond => exact ihFirst.comp F ihSecond
  | tensor hP _ _ hQ ihLeft ihRight =>
      exact (triple_tensor_iff F _ _ _ _).mpr ⟨_, _, _, _, hP, ihLeft, ihRight, hQ⟩
  | feedback I hP _ hQ ih =>
      apply (triple_trace_iff F hF _ _ _).mpr
      exact ⟨I, (tensorTriple_iff F _ _ _).mpr ⟨_, _, hP, ih, hQ⟩⟩

/-- Every valid diagram triple has a derivation, relative to semantic basic-block axioms. -/
theorem Derivable.complete (hF : T.Preserves MonRelCat.symmetricTrace F)
    {X Y} (d : Diagram Atom X Y) {P : F.obj X} {Q : F.obj Y}
    (h : Triple F (d.denote interpret T) P Q) : Derivable interpret F P d Q := by
  induction d with
  | atom block => exact .atom block h
  | seq first second ihFirst ihSecond =>
      obtain ⟨R, hFirst, hSecond⟩ := (triple_comp_iff F _ _ _ _).mp h
      exact .seq (ihFirst hFirst) (ihSecond hSecond)
  | tensor left right ihLeft ihRight =>
      obtain ⟨p, u, q, v, hP, hLeft, hRight, hQ⟩ := (triple_tensor_iff F _ _ _ _).mp h
      exact .tensor hP (ihLeft hLeft) (ihRight hRight) hQ
  | feedback body ih =>
      obtain ⟨I, hBody⟩ := (triple_trace_iff F hF _ _ _).mp h
      obtain ⟨P', Q', hP, hBody, hQ⟩ := (tensorTriple_iff F _ _ _).mp hBody
      exact .feedback I hP (ih hBody) hQ

/-- Soundness and relative completeness for arbitrary typed diagrams. -/
theorem derivable_iff_triple (interpret : ∀ {X Y}, Atom X Y → (X ⟶ Y))
    (T : SymmetricTrace C) (F : C ⥤ MonRelCat.{w}) [F.Monoidal]
    (hF : T.Preserves MonRelCat.symmetricTrace F)
    {X Y} (d : Diagram Atom X Y) (P : F.obj X) (Q : F.obj Y) :
    Derivable interpret F P d Q ↔ Triple F (d.denote interpret T) P Q :=
  ⟨fun h => h.sound hF, fun h => Derivable.complete hF d h⟩

end Cslib.TracedHoare
