/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.ClosedProjection
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.ActionIndexComparison

/-!
# Permuting triple Day convolution generators

Computes the associator-braiding permutation of the first two factors on a triple Day convolution generator. Under the stated Kan-extension and tensor-preservation hypotheses, the formula retains the coefficient braiding and the corresponding symmetric-index comparison.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped ExternalProduct

namespace NativeOmegaPreparation.DayTriplePermutation
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [∀ (F G : I ⥤ V), (tensor I).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ I)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorRight v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 I).prod (Functor.fromPUnit.{0} (𝟙_ I))) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((tensor I).prod (𝟭 I)) d) (tensorRight v)]

/-- The actual partial swap of the first two complete Day factors retains both coupled coend
generators, the full coefficient braiding and the genuine complete index comparison. -/
theorem generator (F S H : DayFunctor I V) (x y z : I) :
    (F.functor.obj x ◁ (DayFunctor.η S H).app (y, z)) ≫
        (DayFunctor.η F (S ⊗ H)).app (x, y ⊗ z) ≫
        ((α_ F S H).inv ≫ ((β_ F S).hom ▷ H) ≫ (α_ S F H).hom).natTrans.app
          (x ⊗ (y ⊗ z)) =
      (α_ (F.functor.obj x) (S.functor.obj y) (H.functor.obj z)).inv ≫
        ((β_ (F.functor.obj x) (S.functor.obj y)).hom ▷ H.functor.obj z) ≫
        (α_ (S.functor.obj y) (F.functor.obj x) (H.functor.obj z)).hom ≫
        (S.functor.obj y ◁ (DayFunctor.η F H).app (x, z)) ≫
        (DayFunctor.η S (F ⊗ H)).app (y, x ⊗ z) ≫
        (S ⊗ (F ⊗ H)).functor.map (DayActionIndex.leftCoefficientComparison x y z).hom := by
  let (P Q : DayFunctor I V) : DayConvolution P.functor Q.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution I V (DayFunctor I V) P Q
  have hw :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      I V (β_ F S).hom H (x ⊗ y) z
  change (DayFunctor.η (F ⊗ S) H).app (x ⊗ y, z) ≫
      ((β_ F S).hom ▷ H).natTrans.app ((x ⊗ y) ⊗ z) =
    ((β_ F S).hom.natTrans.app (x ⊗ y) ▷ H.functor.obj z) ≫
      (DayFunctor.η (S ⊗ F) H).app (x ⊗ y, z) at hw
  have hn := DayConvolution.unit_naturality (S ⊗ F).functor H.functor
    (β_ y x).hom (𝟙 z)
  change ((S ⊗ F).functor.map (β_ y x).hom ⊗ₘ H.functor.map (𝟙 z)) ≫
      (DayFunctor.η (S ⊗ F) H).app (x ⊗ y, z) =
    (DayFunctor.η (S ⊗ F) H).app (y ⊗ x, z) ≫
      ((S ⊗ F) ⊗ H).functor.map ((β_ y x).hom ⊗ₘ 𝟙 z) at hn
  simp only [H.functor.map_id, tensorHom_id] at hn
  have ha := LawfulDayConvolutionMonoidalCategoryStruct.associator_hom_unit_unit
    V S F H y x z
  change ((DayFunctor.η S F).app (y, x) ▷ H.functor.obj z) ≫
      (DayFunctor.η (S ⊗ F) H).app (y ⊗ x, z) ≫
      (α_ S F H).hom.natTrans.app ((y ⊗ x) ⊗ z) =
    (α_ (S.functor.obj y) (F.functor.obj x) (H.functor.obj z)).hom ≫
      (S.functor.obj y ◁ (DayFunctor.η F H).app (x, z)) ≫
      (DayFunctor.η S (F ⊗ H)).app (y, x ⊗ z) ≫
      (S ⊗ (F ⊗ H)).functor.map (α_ y x z).inv at ha
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
  rw [DayClosedProjection.associator_inv_generator_assoc]
  simp only [NatTrans.naturality, NatTrans.naturality_assoc, tensor_obj]
  rw [reassoc_of% hw, ← comp_whiskerRight_assoc, DayClosedProjection.braiding_generator,
    comp_whiskerRight]
  simp only [comp_whiskerRight, Category.assoc]
  rw [reassoc_of% hn]
  simp only [NatTrans.naturality_assoc, tensor_obj]
  rw [reassoc_of% ha]
  simp only [← Functor.map_comp, DayActionIndex.leftCoefficientComparison, Iso.trans_hom,
    Iso.symm_hom, whiskerRightIso_hom]

end NativeOmegaPreparation.DayTriplePermutation
