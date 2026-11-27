/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FunctorSequenceLift
import Mathlib.Tactic.FinCases

/-!
# Precomposition of the original cofiber functor diagram

The whole two-arrow diagram commutes with precomposition of its source
category, including both natural transformations and all three functors.
Its lift into the actual full cofiber-sequence category obeys the same law.
The forgetful inclusion supplies the lift equality from the diagram equality.
-/

public section

open CategoryTheory Limits

universe uA vA uB vB uD vD

namespace CategoryTheory.Waldhausen.SConstruction

universe uX vX uY vY

private theorem precompositionNatTransHExt
    {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    {F G F' G' : X ⥤ Y} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G') (h : ∀ A : X, HEq (α.app A) (β.app A)) :
    HEq α β := by
  apply (conj_eqToHom_iff_heq α β hF hG).mp
  apply NatTrans.ext
  funext A
  rw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app, eqToHom_app]
  exact (conj_eqToHom_iff_heq (α.app A) (β.app A)
    (Functor.congr_obj hF A) (Functor.congr_obj hG A)).mpr (h A)


/-- Precomposing the whole two-arrow diagram retains every original functor and arrow. -/
theorem functorSequenceDiagram_precomp
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {D : Type uD} [Category.{vD} D] (H : A ⥤ B) (F₀ F₁ F₂ : B ⥤ D)
    (i : F₀ ⟶ F₁) (p : F₁ ⟶ F₂) :
    H ⋙ functorSequenceDiagram F₀ F₁ F₂ i p =
      functorSequenceDiagram (H ⋙ F₀) (H ⋙ F₁) (H ⋙ F₂)
        (Functor.whiskerLeft H i) (Functor.whiskerLeft H p) := by
  let L := H ⋙ functorSequenceDiagram F₀ F₁ F₂ i p
  let R := functorSequenceDiagram (H ⋙ F₀) (H ⋙ F₁) (H ⋙ F₂)
    (Functor.whiskerLeft H i) (Functor.whiskerLeft H p)
  have hobj : ∀ X : A, L.obj X = R.obj X := by
    intro X
    let U : ComposableArrows D 2 := L.obj X
    let V : ComposableArrows D 2 := R.obj X
    change U = V
    have h₀ : U.obj' 0 = V.obj' 0 :=
      (functorSequenceDiagram_obj_zero F₀ F₁ F₂ i p (H.obj X)).trans
        (functorSequenceDiagram_obj_zero (H ⋙ F₀) (H ⋙ F₁) (H ⋙ F₂)
          (Functor.whiskerLeft H i) (Functor.whiskerLeft H p) X).symm
    have h₁ : U.obj' 1 = V.obj' 1 :=
      (functorSequenceDiagram_obj_one F₀ F₁ F₂ i p (H.obj X)).trans
        (functorSequenceDiagram_obj_one (H ⋙ F₀) (H ⋙ F₁) (H ⋙ F₂)
          (Functor.whiskerLeft H i) (Functor.whiskerLeft H p) X).symm
    have h₂ : U.obj' 2 = V.obj' 2 :=
      (functorSequenceDiagram_obj_two F₀ F₁ F₂ i p (H.obj X)).trans
        (functorSequenceDiagram_obj_two (H ⋙ F₀) (H ⋙ F₁) (H ⋙ F₂)
          (Functor.whiskerLeft H i) (Functor.whiskerLeft H p) X).symm
    refine ComposableArrows.ext₂ (f := U) (g := V) h₀ h₁ h₂ ?_ ?_
    · apply (conj_eqToHom_iff_heq (U.map' 0 1) (V.map' 0 1) h₀ h₁).mpr
      exact (heq_of_eq (functorSequenceDiagram_map_zero_one F₀ F₁ F₂ i p (H.obj X))).trans
        (heq_of_eq (functorSequenceDiagram_map_zero_one (H ⋙ F₀) (H ⋙ F₁) (H ⋙ F₂)
          (Functor.whiskerLeft H i) (Functor.whiskerLeft H p) X)).symm
    · apply (conj_eqToHom_iff_heq (U.map' 1 2) (V.map' 1 2) h₁ h₂).mpr
      exact (heq_of_eq (functorSequenceDiagram_map_one_two F₀ F₁ F₂ i p (H.obj X))).trans
        (heq_of_eq (functorSequenceDiagram_map_one_two (H ⋙ F₀) (H ⋙ F₁) (H ⋙ F₂)
          (Functor.whiskerLeft H i) (Functor.whiskerLeft H p) X)).symm
  change L = R
  apply Functor.hext
  · exact hobj
  · intro X Y f
    refine precompositionNatTransHExt (hobj X) (hobj Y) _ _ ?_
    intro t
    dsimp only [L, R]
    unfold functorSequenceDiagram
    fin_cases t <;> rfl


private theorem cofiberFunctor_eq_of_forget
    {A : Type uA} [Category.{vA} A] {D : Type uD} [Category.{vD} D]
    [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
    (F G : A ⥤ CofiberSequenceCategory D)
    (h : F ⋙ CofiberSequenceCategory.forget D = G ⋙ CofiberSequenceCategory.forget D) :
    F = G := by
  have hobj (X : A) : F.obj X = G.obj X := by
    apply ObjectProperty.FullSubcategory.ext
    exact Functor.congr_obj h X
  refine Functor.ext hobj ?_
  intro X Y f
  apply (CofiberSequenceCategory.fullyFaithfulForget D).map_injective
  simp only [Functor.map_comp, eqToHom_map]
  exact Functor.congr_hom h f

/-- Precomposing the actual cofiber lift keeps the same entire diagram and cofiber rows. -/
theorem cofiberFunctorSequenceLift_precomp
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
    (H : A ⥤ B) (F₀ F₁ F₂ : B ⥤ D) (i : F₀ ⟶ F₁) (p : F₁ ⟶ F₂)
    (h : ∀ X : B, IsCofiberSequence (i.app X) (p.app X)) :
    H ⋙ cofiberFunctorSequenceLift F₀ F₁ F₂ i p h =
      cofiberFunctorSequenceLift (H ⋙ F₀) (H ⋙ F₁) (H ⋙ F₂)
        (Functor.whiskerLeft H i) (Functor.whiskerLeft H p) (fun X => h (H.obj X)) := by
  apply cofiberFunctor_eq_of_forget
  calc
    (H ⋙ cofiberFunctorSequenceLift F₀ F₁ F₂ i p h) ⋙ CofiberSequenceCategory.forget D =
        H ⋙ cofiberFunctorSequenceLift F₀ F₁ F₂ i p h ⋙ CofiberSequenceCategory.forget D :=
      Functor.assoc _ _ _
    _ = H ⋙ functorSequenceDiagram F₀ F₁ F₂ i p :=
      congrArg (fun F => H ⋙ F) (cofiberFunctorSequenceLift_forget F₀ F₁ F₂ i p h)
    _ = functorSequenceDiagram (H ⋙ F₀) (H ⋙ F₁) (H ⋙ F₂)
        (Functor.whiskerLeft H i) (Functor.whiskerLeft H p) :=
      functorSequenceDiagram_precomp H F₀ F₁ F₂ i p
    _ = cofiberFunctorSequenceLift (H ⋙ F₀) (H ⋙ F₁) (H ⋙ F₂)
        (Functor.whiskerLeft H i) (Functor.whiskerLeft H p) (fun X => h (H.obj X)) ⋙
          CofiberSequenceCategory.forget D :=
      (cofiberFunctorSequenceLift_forget _ _ _ _ _ _).symm

end CategoryTheory.Waldhausen.SConstruction
