/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.TensorUnderlying

/-!
# The actual free-pair bimodule tensor

The original middle scalar remains a coefficient. Its multiplication
contracts the two middle free actions in the chosen coequalizer, and the
original associators identify the result with the outer free bimodule.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped MonoidalCategory

namespace Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasColimitsOfSize.{0, 0} C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (A B D : Mon C)

/-- The complete free-pair coefficient reassociation uses the original four associators. -/
def freePairReassocIso (X Y : C) :
    ((A.X ⊗ X) ⊗ B.X) ⊗ (Y ⊗ D.X) ≅ (freeObject A D (X ⊗ (B.X ⊗ Y))).X :=
  (α_ ((A.X ⊗ X) ⊗ B.X) Y D.X).symm ≪≫
    (tensorRight D.X).mapIso ((α_ (A.X ⊗ X) B.X Y) ≪≫ (α_ A.X X (B.X ⊗ Y)))

/-- The actual two-free bimodule tensor has the original outer free carrier and middle scalar coefficient. -/
def freePairUnderlyingIso (X Y : C) :
    (tensorBimod (freeObject A B X) (freeObject B D Y)).X ≅
      (freeObject A D (X ⊗ (B.X ⊗ Y))).X :=
  tensorFreeUnderlyingIso (freeObject A B X) Y ≪≫ freePairReassocIso A B D X Y

/-- The original quotient projection contracts only the middle action and then reassociates the free carrier. -/
theorem freePairUnderlyingIso_projection (X Y : C) :
    tensorProjection (freeObject A B X) (freeObject B D Y) ≫
        (freePairUnderlyingIso A B D X Y).hom =
      ((freeObject A B X).X ◁ (α_ B.X Y D.X).hom) ≫
        (α_ (freeObject A B X).X B.X (Y ⊗ D.X)).inv ≫
          ((freeObject A B X).actRight ▷ (Y ⊗ D.X)) ≫
            (freePairReassocIso A B D X Y).hom := by
  simpa only [freePairUnderlyingIso, Iso.trans_hom, Category.assoc] using
    congrArg (fun k => k ≫ (freePairReassocIso A B D X Y).hom)
      (tensorFreeUnderlyingIso_projection (freeObject A B X) Y)

/-- The full one-sided free reduction respects the original outer left action of every bimodule. -/
theorem tensorFreeUnderlyingIso_leftAction (M : Bimod A B) (Y : C) :
    (tensorBimod M (freeObject B D Y)).actLeft ≫ (tensorFreeUnderlyingIso (D := D) M Y).hom =
      (A.X ◁ (tensorFreeUnderlyingIso (D := D) M Y).hom) ≫
        (α_ A.X M.X (Y ⊗ D.X)).inv ≫ (M.actLeft ▷ (Y ⊗ D.X)) := by
  let N := freeObject B D Y
  let π := tensorProjection M N
  let : Epi (A.X ◁ π) := by
    change Epi ((tensorLeft A.X).map (coequalizer.π _ _))
    infer_instance
  apply (cancel_epi (A.X ◁ π)).mp
  have hleft : (A.X ◁ π) ≫ (tensorBimod M N).actLeft =
      (α_ A.X M.X N.X).inv ≫ (M.actLeft ▷ N.X) ≫ π :=
    TensorBimod.whiskerLeft_π_actLeft M N
  rw [← Category.assoc, hleft]
  simp only [Category.assoc]
  rw [tensorFreeUnderlyingIso_projection]
  rw [← whiskerLeft_comp_assoc, tensorFreeUnderlyingIso_projection]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc]
  rw [← comp_whiskerRight, M.middle_assoc]
  simp only [comp_whiskerRight]
  rw [associator_inv_naturality_middle_assoc]
  have h :
      (α_ A.X M.X ((B.X ⊗ Y) ⊗ D.X)).inv ≫
        ((A.X ⊗ M.X) ◁ (α_ B.X Y D.X).hom) ≫
          (α_ (A.X ⊗ M.X) B.X (Y ⊗ D.X)).inv ≫
            ((α_ A.X M.X B.X).hom ▷ (Y ⊗ D.X)) =
      (A.X ◁ (M.X ◁ (α_ B.X Y D.X).hom)) ≫
        (A.X ◁ (α_ M.X B.X (Y ⊗ D.X)).inv) ≫
          (α_ A.X (M.X ⊗ B.X) (Y ⊗ D.X)).inv := by monoidal
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ ((A.X ◁ M.actRight) ▷ (Y ⊗ D.X)) ≫ (M.actLeft ▷ (Y ⊗ D.X))) h

/-- The whole free-pair contraction preserves the original outer left action. -/
theorem freePairUnderlyingIso_leftAction (X Y : C) :
    (tensorBimod (freeObject A B X) (freeObject B D Y)).actLeft ≫
        (freePairUnderlyingIso A B D X Y).hom =
      (A.X ◁ (freePairUnderlyingIso A B D X Y).hom) ≫
        (freeObject A D (X ⊗ (B.X ⊗ Y))).actLeft := by
  have h :
      (α_ A.X (freeObject A B X).X (Y ⊗ D.X)).inv ≫
        ((freeObject A B X).actLeft ▷ (Y ⊗ D.X)) ≫
          (freePairReassocIso A B D X Y).hom =
      (A.X ◁ (freePairReassocIso A B D X Y).hom) ≫
        (freeObject A D (X ⊗ (B.X ⊗ Y))).actLeft := by
    dsimp only [freePairReassocIso]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, freeLeftStructure_smul,
      Functor.flip_obj_map, Functor.map_comp, NatTrans.comp_app, curriedTensor_map_app,
      comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    monoidal
  change _ ≫ ((tensorFreeUnderlyingIso (freeObject A B X) Y).hom ≫
    (freePairReassocIso A B D X Y).hom) = _
  rw [← Category.assoc, tensorFreeUnderlyingIso_leftAction]
  simp only [Category.assoc]
  rw [h]
  rw [freePairUnderlyingIso, Iso.trans_hom, whiskerLeft_comp]
  exact (Category.assoc _ _ _).symm

/-- The same full free reduction respects the actual outer right multiplication. -/
theorem tensorFreeUnderlyingIso_rightAction (M : Bimod A B) (Y : C) :
    (tensorBimod M (freeObject B D Y)).actRight ≫ (tensorFreeUnderlyingIso (D := D) M Y).hom =
      ((tensorFreeUnderlyingIso (D := D) M Y).hom ▷ D.X) ≫
        (α_ M.X (Y ⊗ D.X) D.X).hom ≫
          (M.X ◁ ((α_ Y D.X D.X).hom ≫ Y ◁ μ[D.X])) := by
  let N := freeObject B D Y
  let π := tensorProjection M N
  let : Epi (π ▷ D.X) := by
    change Epi ((tensorRight D.X).map (coequalizer.π _ _))
    infer_instance
  apply (cancel_epi (π ▷ D.X)).mp
  have hright : (π ▷ D.X) ≫ (tensorBimod M N).actRight =
      (α_ M.X N.X D.X).hom ≫ M.X ◁ N.actRight ≫ π :=
    TensorBimod.π_tensor_id_actRight M N
  have hN : N.actRight = (α_ (B.X ⊗ Y) D.X D.X).hom ≫ (B.X ⊗ Y) ◁ μ[D.X] :=
    freeObject_actRight B D Y
  rw [← Category.assoc, hright]
  simp only [Category.assoc]
  rw [tensorFreeUnderlyingIso_projection]
  rw [← comp_whiskerRight_assoc, tensorFreeUnderlyingIso_projection, hN]
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  slice_lhs 3 4 =>
    rw [← whiskerLeft_comp, associator_naturality_right, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc]
  rw [associator_naturality_left_assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange]
  have h :
      (α_ M.X ((B.X ⊗ Y) ⊗ D.X) D.X).hom ≫
        (M.X ◁ (α_ (B.X ⊗ Y) D.X D.X).hom) ≫
          (M.X ◁ (α_ B.X Y (D.X ⊗ D.X)).hom) ≫
            (α_ M.X B.X (Y ⊗ (D.X ⊗ D.X))).inv =
      ((M.X ◁ (α_ B.X Y D.X).hom) ▷ D.X) ≫
        ((α_ M.X B.X (Y ⊗ D.X)).inv ▷ D.X) ≫
          (α_ (M.X ⊗ B.X) (Y ⊗ D.X) D.X).hom ≫
            ((M.X ⊗ B.X) ◁ (α_ Y D.X D.X).hom) := by monoidal
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ ((M.X ⊗ B.X) ◁ (Y ◁ μ[D.X])) ≫ (M.actRight ▷ (Y ⊗ D.X))) h

/-- The free-pair coefficient reassociation retains the original outer right action. -/
theorem freePairUnderlyingIso_rightAction (X Y : C) :
    (tensorBimod (freeObject A B X) (freeObject B D Y)).actRight ≫
        (freePairUnderlyingIso A B D X Y).hom =
      ((freePairUnderlyingIso A B D X Y).hom ▷ D.X) ≫
        (freeObject A D (X ⊗ (B.X ⊗ Y))).actRight := by
  have h :
      (α_ (freeObject A B X).X (Y ⊗ D.X) D.X).hom ≫
        ((freeObject A B X).X ◁ ((α_ Y D.X D.X).hom ≫ Y ◁ μ[D.X])) ≫
          (freePairReassocIso A B D X Y).hom =
      ((freePairReassocIso A B D X Y).hom ▷ D.X) ≫
        (freeObject A D (X ⊗ (B.X ⊗ Y))).actRight := by
    dsimp only [freePairReassocIso]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, freeRightStructure_smul,
      Functor.flip_obj_map, Functor.map_comp, NatTrans.comp_app, curriedTensor_map_app,
      comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    monoidal
  change _ ≫ ((tensorFreeUnderlyingIso (freeObject A B X) Y).hom ≫
    (freePairReassocIso A B D X Y).hom) = _
  rw [← Category.assoc, tensorFreeUnderlyingIso_rightAction]
  simp only [Category.assoc]
  rw [h]
  rw [freePairUnderlyingIso, Iso.trans_hom, comp_whiskerRight, Category.assoc]

/-- The actual tensor of the two original free bimodules is the outer free bimodule with its middle scalar. -/
def freePairTensorIso (X Y : C) :
    tensorBimod (freeObject A B X) (freeObject B D Y) ≅
      freeObject A D (X ⊗ (B.X ⊗ Y)) :=
  isoOfIso (freePairUnderlyingIso A B D X Y)
    (freePairUnderlyingIso_leftAction A B D X Y) (freePairUnderlyingIso_rightAction A B D X Y)

/-- The complete free-pair bimodule morphism has the same original underlying quotient contraction. -/
theorem freePairTensorIso_hom (X Y : C) :
    (freePairTensorIso A B D X Y).hom.hom = (freePairUnderlyingIso A B D X Y).hom := rfl

/-- Every original first-variable bimodule map is retained by the full free reduction. -/
theorem tensorFreeUnderlyingIso_coefficient_naturality {M M' : Bimod A B} (f : M ⟶ M') (Y : C) :
    (tensorMap f (𝟙 (freeObject B D Y))).hom ≫ (tensorFreeUnderlyingIso (D := D) M' Y).hom =
      (tensorFreeUnderlyingIso (D := D) M Y).hom ≫ (f.hom ▷ (Y ⊗ D.X)) := by
  apply (cancel_epi (tensorProjection M (freeObject B D Y))).mp
  rw [← Category.assoc, tensorMap_projection]
  simp only [id_hom', tensorHom_id, Category.assoc]
  rw [tensorFreeUnderlyingIso_projection]
  rw [reassoc_of% (tensorFreeUnderlyingIso_projection (D := D) M Y)]
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc]
  rw [← comp_whiskerRight, ← f.right_act_hom, comp_whiskerRight]

/-- Every original second coefficient map is retained, including the actual free left action. -/
theorem tensorFreeUnderlyingIso_generator_naturality (M : Bimod A B) {Y Y' : C} (g : Y ⟶ Y') :
    (tensorMap (𝟙 M) ((free B D).map g)).hom ≫ (tensorFreeUnderlyingIso (D := D) M Y').hom =
      (tensorFreeUnderlyingIso (D := D) M Y).hom ≫ (M.X ◁ (g ▷ D.X)) := by
  apply (cancel_epi (tensorProjection M (freeObject B D Y))).mp
  rw [← Category.assoc, tensorMap_projection]
  simp only [id_hom', id_tensorHom, free_map_hom, Category.assoc]
  change (M.X ◁ ((B.X ◁ g) ▷ D.X)) ≫ tensorProjection M (freeObject B D Y') ≫
    (tensorFreeUnderlyingIso (D := D) M Y').hom =
      tensorProjection M (freeObject B D Y) ≫ (tensorFreeUnderlyingIso (D := D) M Y).hom ≫
        (M.X ◁ (g ▷ D.X))
  rw [tensorFreeUnderlyingIso_projection]
  rw [reassoc_of% (tensorFreeUnderlyingIso_projection (D := D) M Y)]
  rw [← whiskerLeft_comp_assoc, associator_naturality_middle, whiskerLeft_comp_assoc,
    associator_inv_naturality_right_assoc, whisker_exchange]

/-- Both original maps vary in the same complete one-sided tensor reduction. -/
theorem tensorFreeUnderlyingIso_naturality {M M' : Bimod A B} (f : M ⟶ M')
    {Y Y' : C} (g : Y ⟶ Y') :
    (tensorMap f ((free B D).map g)).hom ≫ (tensorFreeUnderlyingIso (D := D) M' Y').hom =
      (tensorFreeUnderlyingIso (D := D) M Y).hom ≫ (f.hom ⊗ₘ (g ▷ D.X)) := by
  have h : tensorMap f ((free B D).map g) =
      tensorMap f (𝟙 (freeObject B D Y)) ≫ tensorMap (𝟙 M') ((free B D).map g) := by
    simp only [tensorMap, whiskerLeft_id_bimod, id_whiskerRight_bimod,
      Category.comp_id, Category.id_comp]
    rfl
  rw [h, comp_hom', Category.assoc, tensorFreeUnderlyingIso_generator_naturality,
    ← Category.assoc, tensorFreeUnderlyingIso_coefficient_naturality,
    Category.assoc, ← tensorHom_def]

omit [HasColimitsOfSize.{0, 0} C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- Both complete coefficient maps commute with the original free-pair reassociation. -/
theorem freePairReassocIso_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (((A.X ◁ f) ▷ B.X) ⊗ₘ (g ▷ D.X)) ≫ (freePairReassocIso A B D X' Y').hom =
      (freePairReassocIso A B D X Y).hom ≫ ((A.X ◁ (f ⊗ₘ (B.X ◁ g))) ▷ D.X) := by
  dsimp only [freePairReassocIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.flip_obj_map,
    Functor.map_comp, NatTrans.comp_app, curriedTensor_map_app, Category.assoc]
  monoidal

/-- The whole free-pair bimodule isomorphism retains both original free-generator maps. -/
theorem freePairTensorIso_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorMap ((free A B).map f) ((free B D).map g) ≫ (freePairTensorIso A B D X' Y').hom =
      (freePairTensorIso A B D X Y).hom ≫ (free A D).map (f ⊗ₘ (B.X ◁ g)) := by
  apply hom_ext
  simp only [comp_hom', freePairTensorIso_hom, freePairUnderlyingIso, Iso.trans_hom]
  have h := congrArg (fun k => k ≫ (freePairReassocIso A B D X' Y').hom)
    (tensorFreeUnderlyingIso_naturality A B D ((free A B).map f) g)
  rw [free_map_hom] at h
  simp only [Category.assoc] at h
  rw [freePairReassocIso_naturality] at h
  simpa only [Category.assoc, free, freeMap] using h

end Bimod
