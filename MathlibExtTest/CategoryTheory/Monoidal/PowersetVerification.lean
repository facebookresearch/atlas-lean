/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.PowersetVerification

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe u
namespace PowersetVerificationTests
open PowersetVerification

example : verification.{u}.Monoidal := inferInstance
example : verification.{u}.Braided := inferInstance
example : SumRelCat.symmetricTrace.{u}.Preserves MonRelCat.symmetricTrace verification :=
  preserves_trace
example (X : SumRelCat.{u}) : verification.map (𝟙 X) = 𝟙 (verification.obj X) :=
  verification.map_id X
example {X Y Z : SumRelCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    verification.map (f ≫ g) = verification.map f ≫ verification.map g :=
  verification.map_comp f g

example {X Y : SumRelCat.{u}} (f : X ⟶ Y) (P : Set X) (Q : Set Y) :
    (P,Q) ∈ (verification.map f).rel ↔ ∀ x ∈ P, ∀ y, (x,y) ∈ f.rel → y ∈ Q := by
  rw [map_rel]
  simp only [Set.subset_def, SetRel.mem_image, forall_exists_index, and_imp]
  aesop

example (X Y : SumRelCat.{u}) (P : Set X) (Q : Set Y) (x : X) :
    Sum.inl x ∈ tensorOrderIso X Y (P,Q) ↔ x ∈ P := by simp [tensorOrderIso]
example (X Y : SumRelCat.{u}) (P : Set X) (Q : Set Y) (y : Y) :
    Sum.inr y ∈ tensorOrderIso X Y (P,Q) ↔ y ∈ Q := by simp [tensorOrderIso]
example (X Y : SumRelCat.{u}) : IsIso (Functor.LaxMonoidal.μ verification X Y) :=
  inferInstance
example : IsIso (Functor.LaxMonoidal.ε verification.{u}) := inferInstance

-- Branching has universal postconditions: one good branch is insufficient.
private def branching : SumRelCat.of Bool ⟶ SumRelCat.of Bool := .ofRel Set.univ
example : (({false} : Set Bool), Set.univ) ∈ (verification.map branching).rel := by
  change branching.rel.image {false} ⊆ Set.univ
  exact Set.subset_univ _
example : (({false} : Set Bool), {false}) ∉ (verification.map branching).rel := by
  intro h
  have bad : true ∈ ({false} : Set Bool) := h ⟨false, by simp, trivial⟩
  simp at bad
example : ((∅ : Set Bool), ∅) ∈ (verification.map branching).rel := by
  change branching.rel.image ∅ ⊆ ∅
  simp

-- A relation with no outputs satisfies every postcondition, even the empty one.
private def abort : SumRelCat.of Bool ⟶ SumRelCat.of Bool := .ofRel ∅
example : ((Set.univ : Set Bool), ∅) ∈ (verification.map abort).rel := by
  change abort.rel.image Set.univ ⊆ ∅
  simp [abort]

-- An infinite hidden carrier with arbitrarily long finite executions.
private def countdown : SumRelCat.of ℕ ⊗ SumRelCat.of ℕ ⟶
    SumRelCat.of ℕ ⊗ SumRelCat.of ℕ := .ofRel {p |
  match p.1, p.2 with
  | .inl n, .inr m => n = m
  | .inr n, .inl y => n = 0 ∧ y = 0
  | .inr n, .inr m => n = m + 1
  | _, _ => False}

private theorem countdown_path (n : ℕ) :
    SumRelCat.FeedbackPath countdown (Sum.inr n) 0 := by
  induction n with
  | zero => exact .output ⟨rfl, rfl⟩
  | succ n ih => exact .step rfl ih

example (n : ℕ) : (n,0) ∈ (SumRelCat.symmetricTrace.trace countdown).rel :=
  SumRelCat.FeedbackPath.step rfl (countdown_path n)

example : countdown.rel.image
    (tensorOrderIso (SumRelCat.of ℕ) (SumRelCat.of ℕ) (Set.univ, Set.univ)) ⊆
      tensorOrderIso (SumRelCat.of ℕ) (SumRelCat.of ℕ) ({0}, Set.univ) := by
  rintro (y | u) ⟨(x | v), _, h⟩
  · exact False.elim h
  · simpa [tensorOrderIso] using h.2
  · simp [tensorOrderIso]
  · simp [tensorOrderIso]

example : ((Set.univ : Set ℕ), {0}) ∈
    (verification.map (SumRelCat.symmetricTrace.trace countdown)).rel := by
  apply (feedback_image_subset_iff countdown Set.univ {0}).mpr
  refine ⟨Set.univ, ?_⟩
  rintro (y | u) ⟨(x | v), _, h⟩
  · exact False.elim h
  · simpa [tensorOrderIso] using h.2
  · simp [tensorOrderIso]
  · simp [tensorOrderIso]

-- The invariant must include the entry states; choosing the empty set fails.
example : ¬ countdown.rel.image
    (tensorOrderIso (SumRelCat.of ℕ) (SumRelCat.of ℕ) (Set.univ, ∅)) ⊆
      tensorOrderIso (SumRelCat.of ℕ) (SumRelCat.of ℕ) ({0}, ∅) := by
  intro h
  have bad := h (show Sum.inr 0 ∈ countdown.rel.image
      (tensorOrderIso (SumRelCat.of ℕ) (SumRelCat.of ℕ) (Set.univ, ∅)) from
    ⟨Sum.inl 0, by simp [tensorOrderIso], rfl⟩)
  simp [tensorOrderIso] at bad

-- Pure hidden looping is divergence, not a total-correctness obligation.
private def noExit : SumRelCat.of Bool ⊗ SumRelCat.of ℕ ⟶
    SumRelCat.of Bool ⊗ SumRelCat.of ℕ := .ofRel {p | ∃ n, p.2 = Sum.inr n}
example : (SumRelCat.feedback noExit).rel = ∅ := by
  apply SumRelCat.feedback_eq_empty_of_no_exit
  intro s y
  rintro ⟨n, h⟩
  cases h
example : ((Set.univ : Set Bool), ∅) ∈
    (verification.map (SumRelCat.feedback noExit)).rel := by
  change (SumRelCat.feedback noExit).rel.image Set.univ ⊆ ∅
  rw [SumRelCat.feedback_eq_empty_of_no_exit noExit (by
    intro s y
    rintro ⟨n, h⟩
    cases h)]
  simp

-- The full invariant equivalence and comparison-aware trace API remain usable.
example {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) (P : Set X) (R : Set Y) :
    (P,R) ∈ (verification.map (SumRelCat.symmetricTrace.trace f)).rel ↔
      ∃ Q : Set U, f.rel.image (tensorOrderIso X U (P,Q)) ⊆ tensorOrderIso Y U (R,Q) :=
  feedback_image_subset_iff f P R
example {X Y U : SumRelCat.{u}} (f : X ⊗ U ⟶ Y ⊗ U) :
    verification.map (SumRelCat.symmetricTrace.trace f) =
      MonRelCat.symmetricTrace.trace (Functor.LaxMonoidal.μ verification X U ≫
        verification.map f ≫ Functor.OplaxMonoidal.δ verification Y U) := preserves_trace f
example (P Q : Set PEmpty) :
    (P,Q) ∈ (verification.map (𝟙 (SumRelCat.of PEmpty))).rel := by
  change SetRel.id.image P ⊆ Q
  simp

#print axioms CategoryTheory.PowersetVerification.preserves_trace
#print axioms CategoryTheory.PowersetVerification.coreMonoidal
end PowersetVerificationTests
