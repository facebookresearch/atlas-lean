/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.SumRelCat
public import Mathlib.Logic.Relation
/-!
# Finite-path feedback for disjoint-union relations

Feedback relates an input to an output precisely when a finite execution reaches
that output, making any finite number of visits to the hidden summand. Infinite
loops alone contribute no output. No finiteness, determinism or termination
assumption is imposed on the relation or its sets.

The closure characterization is the formula A union B D-star C of Joyal, Street
and Verity, Traced monoidal categories (1996), Proposition 6.3,
https://doi.org/10.1017/S0305004100074338. Relational composition below is written
in Mathlib's forward order. This module establishes the operation and its path
semantics; the symmetric trace axioms are a separate construction.
-/

@[expose] public section
open CategoryTheory MonoidalCategory
namespace CategoryTheory.SumRelCat
universe u
variable {X Y U : SumRelCat.{u}}
/-- A finite execution that eventually leaves through the external output. -/
inductive FeedbackPath (f : X ⊗ U ⟶ Y ⊗ U) : Sum X U → Y → Prop
  /-- Exit immediately through the external output. -/
  | output {s y} : (s, Sum.inl y) ∈ f.rel → FeedbackPath f s y
  /-- Enter the feedback summand and continue a finite execution. -/
  | step {s v y} : (s, Sum.inr v) ∈ f.rel →
      FeedbackPath f (Sum.inr v) y → FeedbackPath f s y
/-- Relational feedback includes exactly the terminating finite executions. -/
def feedback (f : X ⊗ U ⟶ Y ⊗ U) : X ⟶ Y :=
  .ofRel {p | FeedbackPath f (Sum.inl p.1) p.2}

/-- An execution consists of a direct edge or entry, finitely many hidden edges, and exit. -/
theorem feedbackPath_iff (f : X ⊗ U ⟶ Y ⊗ U) (s : Sum X U) (y : Y) :
    FeedbackPath f s y ↔ (s, Sum.inl y) ∈ f.rel ∨
      ∃ a b : U, (s, Sum.inr a) ∈ f.rel ∧
        Relation.ReflTransGen (fun a b : U => (Sum.inr a, Sum.inr b) ∈ f.rel) a b ∧
        (Sum.inr b, Sum.inl y) ∈ f.rel := by
  constructor
  · intro h
    induction h with
    | output h => exact Or.inl h
    | @step s v y h _ ih =>
      rcases ih with h' | ⟨a, b, ha, hab, hb⟩
      · exact Or.inr ⟨v, v, h, .refl, h'⟩
      · exact Or.inr ⟨v, b, h, hab.head ha, hb⟩
  · rintro (h | ⟨a, b, ha, hab, hb⟩)
    · exact .output h
    · have path : FeedbackPath f (Sum.inr a) y := by
        clear ha
        induction hab using Relation.ReflTransGen.head_induction_on with
        | refl => exact .output hb
        | head h _ ih => exact .step h ih
      exact .step ha path

/-- Adding edges preserves every terminating execution. -/
theorem FeedbackPath.mono {f g : X ⊗ U ⟶ Y ⊗ U} (h : f.rel ⊆ g.rel)
    {s : Sum X U} {y : Y} (hp : FeedbackPath f s y) : FeedbackPath g s y := by
  induction hp with
  | output hp => exact .output (h hp)
  | step hp _ ih => exact .step (h hp) ih

/-- Relational feedback is monotone in its transition relation. -/
theorem feedback_mono {f g : X ⊗ U ⟶ Y ⊗ U} (h : f.rel ⊆ g.rel) :
    (feedback f).rel ⊆ (feedback g).rel := by
  rintro ⟨x, y⟩ hp
  exact FeedbackPath.mono h hp

/-- The entry, hidden closure and exit characterization of feedback. -/
theorem feedback_rel (f : X ⊗ U ⟶ Y ⊗ U) (x : X) (y : Y) :
    (x, y) ∈ (feedback f).rel ↔ (Sum.inl x, Sum.inl y) ∈ f.rel ∨
      ∃ a b : U, (Sum.inl x, Sum.inr a) ∈ f.rel ∧
        Relation.ReflTransGen (fun a b : U => (Sum.inr a, Sum.inr b) ∈ f.rel) a b ∧
        (Sum.inr b, Sum.inl y) ∈ f.rel := feedbackPath_iff f _ _

/-- Empty feedback leaves only direct input-to-output edges. -/
theorem feedback_zero (f : X ⊗ zero ⟶ Y ⊗ zero) (x : X) (y : Y) :
    (x, y) ∈ (feedback f).rel ↔ (Sum.inl x, Sum.inl y) ∈ f.rel := by
  rw [feedback_rel]
  simp
/-- A terminating execution either exits now or takes a hidden step and then exits. -/
theorem feedbackPath_unfold (f : X ⊗ U ⟶ Y ⊗ U) (s : Sum X U) (y : Y) :
    FeedbackPath f s y ↔ (s, Sum.inl y) ∈ f.rel ∨
      ∃ a : U, (s, Sum.inr a) ∈ f.rel ∧ FeedbackPath f (Sum.inr a) y := by
  constructor
  · intro h
    cases h with
    | output h => exact Or.inl h
    | step h hp => exact Or.inr ⟨_, h, hp⟩
  · rintro (h | ⟨a, h, hp⟩)
    · exact .output h
    · exact .step h hp

/-- Every relation closed under output and feedback steps contains all finite executions. -/
theorem FeedbackPath.least {f : X ⊗ U ⟶ Y ⊗ U} {Q : Sum X U → Y → Prop}
    (output : ∀ s y, (s, Sum.inl y) ∈ f.rel → Q s y)
    (step : ∀ s a y, (s, Sum.inr a) ∈ f.rel → Q (Sum.inr a) y → Q s y)
    {s : Sum X U} {y : Y} (h : FeedbackPath f s y) : Q s y := by
  induction h with
  | output h => exact output _ _ h
  | step h _ ih => exact step _ _ _ h ih

/-- Even cycles cannot produce an output when the relation has no exit edge. -/
theorem feedback_eq_empty_of_no_exit (f : X ⊗ U ⟶ Y ⊗ U)
    (h : ∀ s y, (s, Sum.inl y) ∉ f.rel) : (feedback f).rel = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨x, y⟩ hp
  exact FeedbackPath.least (Q := fun _ _ => False) (fun s y hy => h s y hy)
    (fun _ _ _ _ hi => hi) hp

/-- The JSV block formula, using forward relational composition and reflexive-transitive closure. -/
theorem feedback_eq_blocks (f : X ⊗ U ⟶ Y ⊗ U) :
    (feedback f).rel =
      (inl X U ≫ f ≫ fst Y U).rel ∪
        ((inl X U ≫ f ≫ snd Y U).rel.comp
          {p | Relation.ReflTransGen
            (fun a b : U => (a, b) ∈ (inr X U ≫ f ≫ snd Y U).rel) p.1 p.2}).comp
          (inr X U ≫ f ≫ fst Y U).rel := by
  ext ⟨x, y⟩
  simp only [Set.mem_union, rel_comp, SetRel.comp, Set.mem_ofPred_eq,
    fst_rel_eq, snd_rel_eq, inl_rel_eq, inr_rel_eq]
  rw [feedback_rel]
  aesop

/-- With no edge into feedback, all accepted edges are direct. -/
theorem feedback_rel_of_no_entry (f : X ⊗ U ⟶ Y ⊗ U)
    (h : ∀ x a, (Sum.inl x, Sum.inr a) ∉ f.rel) (x : X) (y : Y) :
    (x, y) ∈ (feedback f).rel ↔ (Sum.inl x, Sum.inl y) ∈ f.rel := by
  rw [feedback_rel]
  simp [h]

/-- A separate hidden endomorphism has no effect on the visible relation. -/
@[simp] theorem feedback_tensor (f : X ⟶ Y) (g : U ⟶ U) : feedback (f ⊗ₘ g) = f := by
  apply Hom.ext
  ext ⟨x, y⟩
  rw [feedback_rel_of_no_entry (f ⊗ₘ g) (by intro x a; simp)]
  simp

end CategoryTheory.SumRelCat
