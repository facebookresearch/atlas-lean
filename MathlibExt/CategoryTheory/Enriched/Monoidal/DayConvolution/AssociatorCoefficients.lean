/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorFaces

/-!
# Product and coefficient associators for the genuine enriched Day tensor

The comparison retains the original enriched product Hom objects, coefficient
tensor words and chosen weighted-coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uA uB uC

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace CategoryTheory.EnrichedDayKernel.Associator

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  {C : Type uC} [EnrichedCategory V C]

attribute [local instance] Enriched.prodCategory

/-- Rebracket the actual enriched product, using the whole Hom-object associator. -/
def productAssociator : EnrichedFunctor V ((A × B) × C) (A × (B × C)) where
  obj X := (X.1.1, (X.1.2, X.2))
  map X Y := (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2)
    (X.2 ⟶[V] Y.2)).hom
  map_id X := by
    change ((λ_ (𝟙_ V)).inv ≫
        (((λ_ (𝟙_ V)).inv ≫ (eId V X.1.1 ⊗ₘ eId V X.1.2)) ⊗ₘ eId V X.2)) ≫
        (α_ (X.1.1 ⟶[V] X.1.1) (X.1.2 ⟶[V] X.1.2)
          (X.2 ⟶[V] X.2)).hom =
      (λ_ (𝟙_ V)).inv ≫
        (eId V X.1.1 ⊗ₘ ((λ_ (𝟙_ V)).inv ≫ (eId V X.1.2 ⊗ₘ eId V X.2)))
    monoidal
  map_comp X Y Z := by
    let f := eComp V X.1.1 Y.1.1 Z.1.1
    let g := eComp V X.1.2 Y.1.2 Z.1.2
    let h := eComp V X.2 Y.2 Z.2
    let X1 := X.1.1 ⟶[V] Y.1.1
    let X2 := X.1.2 ⟶[V] Y.1.2
    let X3 := X.2 ⟶[V] Y.2
    let Y1 := Y.1.1 ⟶[V] Z.1.1
    let Y2 := Y.1.2 ⟶[V] Z.1.2
    let Y3 := Y.2 ⟶[V] Z.2
    change (tensorμ (X1 ⊗ X2) X3 (Y1 ⊗ Y2) Y3 ≫
        ((tensorμ X1 X2 Y1 Y2 ≫ (f ⊗ₘ g)) ⊗ₘ h)) ≫
        (α_ (X.1.1 ⟶[V] Z.1.1) (X.1.2 ⟶[V] Z.1.2)
          (X.2 ⟶[V] Z.2)).hom =
      ((α_ X1 X2 X3).hom ⊗ₘ (α_ Y1 Y2 Y3).hom) ≫
        tensorμ X1 (X2 ⊗ X3) Y1 (Y2 ⊗ Y3) ≫
          (f ⊗ₘ (tensorμ X2 X3 Y2 Y3 ≫ (g ⊗ₘ h)))
    have hleft :
        (tensorμ X1 X2 Y1 Y2 ≫ (f ⊗ₘ g)) ⊗ₘ h =
          (tensorμ X1 X2 Y1 Y2 ▷ (X3 ⊗ Y3)) ≫ ((f ⊗ₘ g) ⊗ₘ h) := by
      rw [← tensorHom_id, tensorHom_comp_tensorHom]
      simp only [Category.id_comp]
    have hright :
        f ⊗ₘ (tensorμ X2 X3 Y2 Y3 ≫ (g ⊗ₘ h)) =
          ((X1 ⊗ Y1) ◁ tensorμ X2 X3 Y2 Y3) ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom]
      simp only [Category.id_comp]
    rw [hleft, hright]
    simp only [Category.assoc]
    rw [associator_naturality]
    rw [associator_monoidal_assoc]

/-- The product associator keeps all three original objects. -/
@[simp]
theorem productAssociator_obj (X : (A × B) × C) :
    (productAssociator (V := V) (A := A) (B := B) (C := C)).obj X =
      (X.1.1, (X.1.2, X.2)) := rfl

/-- The product associator acts on the entire three-factor enriched Hom object. -/
theorem productAssociator_map (X Y : (A × B) × C) :
    (productAssociator (V := V) (A := A) (B := B) (C := C)).map X Y =
      (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2)
        (X.2 ⟶[V] Y.2)).hom := rfl

section Coefficients

open scoped MonoidalClosed

variable [MonoidalClosed V]
  (F : EnrichedFunctor V A V) (G : EnrichedFunctor V B V)
  (H : EnrichedFunctor V C V)

private abbrev selfHom (X Y : V) : V :=
  @EnrichedCategory.Hom V _ _ V (inferInstance : EnrichedCategory V V) X Y

/-- The actual left-associated coefficient functor on the original triple index. -/
abbrev leftCoefficients : EnrichedFunctor V ((A × B) × C) V :=
  (F.externalTensor G).externalTensor H

/-- The actual right-associated coefficient functor, reindexed by the full product associator. -/
abbrev rightCoefficients : EnrichedFunctor V ((A × B) × C) V :=
  (productAssociator (V := V) (A := A) (B := B) (C := C)).comp V
    (F.externalTensor (G.externalTensor H))

/-- The actual coefficient associator is natural on every full original enriched Hom object. -/
@[reassoc]
theorem coefficients_naturality (X Y : (A × B) × C) :
    MonoidalClosed.uncurry ((leftCoefficients F G H).map X Y) ≫
        (α_ (F.obj Y.1.1) (G.obj Y.1.2) (H.obj Y.2)).hom =
      ((α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom ⊗ₘ
        𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((rightCoefficients F G H).map X Y) := by
  let d := MonoidalClosed.enrichedMonoidalCategoryDataSelf V
  let P := (F.map X.1.1 Y.1.1 ⊗ₘ G.map X.1.2 Y.1.2) ⊗ₘ H.map X.2 Y.2
  let L := (d.tensorMap (F.obj X.1.1) (F.obj Y.1.1)
      (G.obj X.1.2) (G.obj Y.1.2) ▷ (selfHom (H.obj X.2) (H.obj Y.2))) ≫
    d.tensorMap (F.obj X.1.1 ⊗ G.obj X.1.2) (F.obj Y.1.1 ⊗ G.obj Y.1.2)
      (H.obj X.2) (H.obj Y.2)
  let R := (α_ (selfHom (F.obj X.1.1) (F.obj Y.1.1))
      (selfHom (G.obj X.1.2) (G.obj Y.1.2)) (selfHom (H.obj X.2) (H.obj Y.2))).hom ≫
    ((selfHom (F.obj X.1.1) (F.obj Y.1.1)) ◁
      d.tensorMap (G.obj X.1.2) (G.obj Y.1.2) (H.obj X.2) (H.obj Y.2)) ≫
    d.tensorMap (F.obj X.1.1) (F.obj Y.1.1)
      (G.obj X.1.2 ⊗ H.obj X.2) (G.obj Y.1.2 ⊗ H.obj Y.2)
  have hL : P ≫ L = (leftCoefficients F G H).map X Y := by
    change ((F.map X.1.1 Y.1.1 ⊗ₘ G.map X.1.2 Y.1.2) ⊗ₘ H.map X.2 Y.2) ≫
        (d.tensorMap (F.obj X.1.1) (F.obj Y.1.1)
          (G.obj X.1.2) (G.obj Y.1.2) ▷ (selfHom (H.obj X.2) (H.obj Y.2))) ≫
        d.tensorMap (F.obj X.1.1 ⊗ G.obj X.1.2) (F.obj Y.1.1 ⊗ G.obj Y.1.2)
          (H.obj X.2) (H.obj Y.2) =
      (((F.map X.1.1 Y.1.1 ⊗ₘ G.map X.1.2 Y.1.2) ≫
          d.tensorMap (F.obj X.1.1) (F.obj Y.1.1) (G.obj X.1.2) (G.obj Y.1.2)) ⊗ₘ
          H.map X.2 Y.2) ≫
        d.tensorMap (F.obj X.1.1 ⊗ G.obj X.1.2) (F.obj Y.1.1 ⊗ G.obj Y.1.2)
          (H.obj X.2) (H.obj Y.2)
    rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id]
  have hR : P ≫ R = (rightCoefficients F G H).map X Y := by
    change P ≫
        (α_ (selfHom (F.obj X.1.1) (F.obj Y.1.1))
          (selfHom (G.obj X.1.2) (G.obj Y.1.2))
          (selfHom (H.obj X.2) (H.obj Y.2))).hom ≫
        ((selfHom (F.obj X.1.1) (F.obj Y.1.1)) ◁
          d.tensorMap (G.obj X.1.2) (G.obj Y.1.2) (H.obj X.2) (H.obj Y.2)) ≫
        d.tensorMap (F.obj X.1.1) (F.obj Y.1.1)
          (G.obj X.1.2 ⊗ H.obj X.2) (G.obj Y.1.2 ⊗ H.obj Y.2) =
      (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)).hom ≫
        (F.map X.1.1 Y.1.1 ⊗ₘ ((G.map X.1.2 Y.1.2 ⊗ₘ H.map X.2 Y.2) ≫
          d.tensorMap (G.obj X.1.2) (G.obj Y.1.2) (H.obj X.2) (H.obj Y.2))) ≫
        d.tensorMap (F.obj X.1.1) (F.obj Y.1.1)
          (G.obj X.1.2 ⊗ H.obj X.2) (G.obj Y.1.2 ⊗ H.obj Y.2)
    dsimp only [P]
    rw [associator_naturality_assoc, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, Category.comp_id]
  have hd := d.associatorNaturality (F.obj X.1.1) (F.obj Y.1.1)
    (G.obj X.1.2) (G.obj Y.1.2) (H.obj X.2) (H.obj Y.2)
  have hw := unitGradedNaturality_eq_whisker L R
    (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom
    (α_ (F.obj Y.1.1) (G.obj Y.1.2) (H.obj Y.2)).hom hd
  have hp :
      (leftCoefficients F G H).map X Y ≫ eHomWhiskerLeft V _
          (α_ (F.obj Y.1.1) (G.obj Y.1.2) (H.obj Y.2)).hom =
        (rightCoefficients F G H).map X Y ≫ eHomWhiskerRight V
          (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom _ := by
    calc
      _ = (P ≫ L) ≫ eHomWhiskerLeft V _
          (α_ (F.obj Y.1.1) (G.obj Y.1.2) (H.obj Y.2)).hom :=
        congrArg (fun k => k ≫ eHomWhiskerLeft V _
          (α_ (F.obj Y.1.1) (G.obj Y.1.2) (H.obj Y.2)).hom) hL.symm
      _ = P ≫ (L ≫ eHomWhiskerLeft V _
          (α_ (F.obj Y.1.1) (G.obj Y.1.2) (H.obj Y.2)).hom) := Category.assoc _ _ _
      _ = P ≫ (R ≫ eHomWhiskerRight V
          (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom _) :=
        congrArg (fun k => P ≫ k) hw
      _ = (P ≫ R) ≫ eHomWhiskerRight V
          (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom _ :=
        (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun k => k ≫ eHomWhiskerRight V
          (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom _) hR
  dsimp only [leftCoefficients, rightCoefficients, EnrichedFunctor.externalTensor,
    EnrichedFunctor.comp, productAssociator] at hp
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at hp
  have hu := congrArg MonoidalClosed.uncurry hp
  dsimp only [leftCoefficients, rightCoefficients, EnrichedFunctor.externalTensor,
    EnrichedFunctor.comp, productAssociator]
  simp only [MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_pre_app] at hu
  rw [tensorHom_id]
  exact hu

/-- The coefficient associator retains the full unit-graded enriched naturality equation. -/
@[no_expose]
def coefficientsGraded :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (leftCoefficients F G H) (rightCoefficients F G H) :=
  GradedNatTrans.unitOfComponents
    (fun X => (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom)
    (fun X Y => coefficients_naturality F G H X Y)

private theorem coefficientsGraded_app_private (X : (A × B) × C) :
    (coefficientsGraded F G H).app X =
      eHomEquiv V (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom :=
  GradedNatTrans.unitOfComponents_app _ _ X

/-- The forward coefficient component is exactly the original coefficient associator. -/
@[simp]
theorem coefficientsGraded_app (X : (A × B) × C) :
    (coefficientsGraded F G H).app X =
      eHomEquiv V (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom :=
  coefficientsGraded_app_private F G H X

/-- The coefficient inverse retains full Hom naturality in the opposite direction. -/
@[reassoc]
theorem coefficients_inv_naturality (X Y : (A × B) × C) :
    MonoidalClosed.uncurry ((rightCoefficients F G H).map X Y) ≫
        (α_ (F.obj Y.1.1) (G.obj Y.1.2) (H.obj Y.2)).inv =
      ((α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).inv ⊗ₘ
        𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((leftCoefficients F G H).map X Y) := by
  apply (cancel_epi
    ((α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom ⊗ₘ 𝟙 (X ⟶[V] Y))).1
  have hn := coefficients_naturality F G H X Y
  dsimp only [leftCoefficients, rightCoefficients, EnrichedFunctor.externalTensor,
    EnrichedFunctor.comp, productAssociator] at hn ⊢
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc,
    Iso.hom_inv_id, Category.comp_id, id_tensorHom_id, Category.id_comp]

/-- The original inverse coefficient associator is a genuine unit-graded transformation. -/
@[no_expose]
def coefficientsInvGraded :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (rightCoefficients F G H) (leftCoefficients F G H) :=
  GradedNatTrans.unitOfComponents
    (fun X => (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).inv)
    (fun X Y => coefficients_inv_naturality F G H X Y)

private theorem coefficientsInvGraded_app_private (X : (A × B) × C) :
    (coefficientsInvGraded F G H).app X =
      eHomEquiv V (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).inv :=
  GradedNatTrans.unitOfComponents_app _ _ X

/-- The inverse coefficient component is exactly the original inverse associator. -/
@[simp]
theorem coefficientsInvGraded_app (X : (A × B) × C) :
    (coefficientsInvGraded F G H).app X =
      eHomEquiv V (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).inv :=
  coefficientsInvGraded_app_private F G H X

private theorem coefficientsGraded_component_private (X : (A × B) × C) :
    (eHomEquiv V).symm ((coefficientsGraded F G H).app X) =
      (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom :=
  GradedNatTrans.unitOfComponents_component _ _ X

private theorem coefficientsInvGraded_component_private (X : (A × B) × C) :
    (eHomEquiv V).symm ((coefficientsInvGraded F G H).app X) =
      (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).inv :=
  GradedNatTrans.unitOfComponents_component _ _ X

/-- The actual left and right coefficient words are isomorphic by genuine
enriched transformations. -/
@[no_expose]
def coefficientIso :
    (⟨leftCoefficients F G H⟩ : EnrichedFunctorCat V ((A × B) × C)) ≅
      ⟨rightCoefficients F G H⟩ where
  hom := coefficientsGraded F G H
  inv := coefficientsInvGraded F G H
  hom_inv_id := by
    apply EnrichedFunctorCat.hom_ext
    intro X
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_id]
    change (eHomEquiv V).symm ((coefficientsGraded F G H).app X) ≫
      (eHomEquiv V).symm ((coefficientsInvGraded F G H).app X) = _
    rw [coefficientsGraded_component_private, coefficientsInvGraded_component_private]
    exact (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom_inv_id
  inv_hom_id := by
    apply EnrichedFunctorCat.hom_ext
    intro X
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_id]
    change (eHomEquiv V).symm ((coefficientsInvGraded F G H).app X) ≫
      (eHomEquiv V).symm ((coefficientsGraded F G H).app X) = _
    rw [coefficientsInvGraded_component_private, coefficientsGraded_component_private]
    exact (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).inv_hom_id

end Coefficients

end CategoryTheory.EnrichedDayKernel.Associator
