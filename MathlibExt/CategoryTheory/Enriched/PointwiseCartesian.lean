/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.PointwiseTensor
public import MathlibExt.CategoryTheory.Enriched.PointwiseFiniteInstances
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Actual pointwise cartesian tensor on genuine enriched functors

The tensor object is the original external tensor restricted along the
cartesian enriched diagonal. Its original coefficient projections give a
binary product on the genuine enriched category. These particular products
construct the monoidal structure; their right adjoints are the actual
Kan-end/external-end composites.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe uA uV vV

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.PointwiseCartesian

variable {V : Type uV} [Category.{vV} V] [CartesianMonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

attribute [local instance] Enriched.prodCategory

/-- The literal diagonal-restricted external tensor object. -/
abbrev tensorObject (F G : EnrichedFunctorCat V A) : EnrichedFunctorCat V A :=
  (PointwiseTensor.leftTensor PointwiseTensor.cartesianDiagonal F).obj G

/-- Each tensor value is the actual selected coefficient product. -/
@[simp]
theorem tensorObject_obj (F G : EnrichedFunctorCat V A) (a : A) :
    (tensorObject F G).toEnrichedFunctor.obj a =
      F.toEnrichedFunctor.obj a ⊗ G.toEnrichedFunctor.obj a := rfl

omit [MonoidalClosed V] in
private theorem action_fst {X Y X' Y' H : V} (f : X ⊗ H ⟶ X') (g : Y ⊗ H ⟶ Y') :
    ((X ⊗ Y) ◁ lift (𝟙 H) (𝟙 H)) ≫ tensorμ X Y H H ≫
      (f ⊗ₘ g) ≫ fst X' Y' = (fst X Y ⊗ₘ 𝟙 H) ≫ f := by
  rw [tensorHom_fst, ← Category.assoc _ _ f, tensorμ_fst]
  rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp, lift_fst]

omit [MonoidalClosed V] in
private theorem action_snd {X Y X' Y' H : V} (f : X ⊗ H ⟶ X') (g : Y ⊗ H ⟶ Y') :
    ((X ⊗ Y) ◁ lift (𝟙 H) (𝟙 H)) ≫ tensorμ X Y H H ≫
      (f ⊗ₘ g) ≫ snd X' Y' = (snd X Y ⊗ₘ 𝟙 H) ≫ g := by
  rw [tensorHom_snd, ← Category.assoc _ _ g, tensorμ_snd]
  rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp, lift_snd]

set_option backward.isDefEq.respectTransparency false in
/-- The complete tensor Hom action projects to the original first action. -/
theorem tensor_action_fst (F G : EnrichedFunctorCat V A) (a b : A) :
    MonoidalClosed.uncurry ((tensorObject F G).toEnrichedFunctor.map a b) ≫
      fst (F.toEnrichedFunctor.obj b) (G.toEnrichedFunctor.obj b) =
    (fst (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) := by
  rw [PointwiseTensor.leftTensor_fullHom, MonoidalClosed.uncurry_natural_left,
    EnrichedFunctor.externalTensor_uncurry]
  simpa only [PointwiseTensor.cartesianDiagonal_obj, PointwiseTensor.cartesianDiagonal_map,
    tensorObject_obj, Category.assoc] using
    (action_fst (MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b))
      (MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b)))

set_option backward.isDefEq.respectTransparency false in
/-- The other entire Hom action projects to the same original second action. -/
theorem tensor_action_snd (F G : EnrichedFunctorCat V A) (a b : A) :
    MonoidalClosed.uncurry ((tensorObject F G).toEnrichedFunctor.map a b) ≫
      snd (F.toEnrichedFunctor.obj b) (G.toEnrichedFunctor.obj b) =
    (snd (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b) := by
  rw [PointwiseTensor.leftTensor_fullHom, MonoidalClosed.uncurry_natural_left,
    EnrichedFunctor.externalTensor_uncurry]
  simpa only [PointwiseTensor.cartesianDiagonal_obj, PointwiseTensor.cartesianDiagonal_map,
    tensorObject_obj, Category.assoc] using
    (action_snd (MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b))
      (MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b)))

/-- The original first coefficient projection is a genuine full-Hom transformation. -/
def firstProjection (F G : EnrichedFunctorCat V A) : tensorObject F G ⟶ F :=
  GradedNatTrans.unitOfComponents
    (fun a => fst (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a))
    (tensor_action_fst F G)

/-- The original second projection retains full enriched naturality. -/
def secondProjection (F G : EnrichedFunctorCat V A) : tensorObject F G ⟶ G :=
  GradedNatTrans.unitOfComponents
    (fun a => snd (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a))
    (tensor_action_snd F G)

/-- First projection evaluates to the selected base product projection. -/
theorem firstProjection_component (F G : EnrichedFunctorCat V A) (a : A) :
    component (firstProjection F G) a =
      fst (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a) :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- Second projection is the selected original base product projection. -/
theorem secondProjection_component (F G : EnrichedFunctorCat V A) (a : A) :
    component (secondProjection F G) a =
      snd (F.toEnrichedFunctor.obj a) (G.toEnrichedFunctor.obj a) :=
  GradedNatTrans.unitOfComponents_component _ _ a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The selected pointwise product lift retains the two entire original input maps. -/
def liftMap {Z F G : EnrichedFunctorCat V A} (f : Z ⟶ F) (g : Z ⟶ G) : Z ⟶ tensorObject F G :=
  GradedNatTrans.unitOfComponents (fun a => lift (component f a) (component g a)) (by
    intro a b
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.assoc]
      erw [tensor_action_fst]
      erw [tensorHom_comp_tensorHom_assoc, lift_fst, Category.id_comp]
      exact f.uncurriedNaturality a b
    · rw [Category.assoc, lift_snd, Category.assoc]
      erw [tensor_action_snd]
      erw [tensorHom_comp_tensorHom_assoc, lift_snd, Category.id_comp]
      exact g.uncurriedNaturality a b)

/-- The whole lift has the original coefficient product map at every object. -/
theorem liftMap_component {Z F G : EnrichedFunctorCat V A} (f : Z ⟶ F) (g : Z ⟶ G) (a : A) :
    component (liftMap f g) a = lift (component f a) (component g a) :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The full first factor equation holds in the genuine enriched functor category. -/
theorem liftMap_first {Z F G : EnrichedFunctorCat V A} (f : Z ⟶ F) (g : Z ⟶ G) :
    liftMap f g ≫ firstProjection F G = f := by
  apply hom_ext
  intro a
  rw [component_comp, firstProjection_component, liftMap_component]
  exact lift_fst _ _

/-- The full second factor equation uses the same original product lift. -/
theorem liftMap_second {Z F G : EnrichedFunctorCat V A} (f : Z ⟶ F) (g : Z ⟶ G) :
    liftMap f g ≫ secondProjection F G = g := by
  apply hom_ext
  intro a
  rw [component_comp, secondProjection_component, liftMap_component]
  exact lift_snd _ _

/-- These exact full-Hom projection maps form the selected genuine binary product. -/
def binaryFan (F G : EnrichedFunctorCat V A) : BinaryFan F G :=
  BinaryFan.mk (firstProjection F G) (secondProjection F G)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual diagonal tensor and original projections have the full product universal property. -/
def binaryIsLimit (F G : EnrichedFunctorCat V A) : IsLimit (binaryFan F G) :=
  BinaryFan.IsLimit.mk _ (fun f g => liftMap f g)
    (fun f g => liftMap_first f g) (fun f g => liftMap_second f g)
    (fun f g m hf hg => by
      apply hom_ext
      intro a
      erw [liftMap_component]
      apply CartesianMonoidalCategory.hom_ext
      · erw [lift_fst]
        have h := congrArg (fun q => component q a)
          (show m ≫ firstProjection F G = f from hf)
        rw [component_comp] at h
        erw [firstProjection_component] at h
        simpa only [PointwiseTensor.cartesianDiagonal_obj] using h
      · erw [lift_snd]
        have h := congrArg (fun q => component q a)
          (show m ≫ secondProjection F G = g from hg)
        rw [component_comp] at h
        erw [secondProjection_component] at h
        simpa only [PointwiseTensor.cartesianDiagonal_obj] using h)

variable [HasTerminal (EnrichedFunctorCat V A)]

/-- Construct the genuine pointwise tensor monoidal structure from those exact products. -/
@[instance_reducible]
def monoidalCategory : CartesianMonoidalCategory (EnrichedFunctorCat V A) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    (getLimitCone (Functor.empty (EnrichedFunctorCat V A)))
    (fun F G => ⟨binaryFan F G, binaryIsLimit F G⟩)

/-- The monoidal tensor object is literally the original diagonal-restricted external tensor. -/
theorem monoidal_tensorObject (F G : EnrichedFunctorCat V A) :
    letI := monoidalCategory (V := V) (A := A)
    F ⊗ G = tensorObject F G := rfl

attribute [local instance] monoidalCategory

/-- The braiding induced by the chosen pointwise cartesian products of enriched functors. -/
local instance diagramBraided : BraidedCategory (EnrichedFunctorCat V A) :=
  BraidedCategory.ofCartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The monoidal left tensor is the same entire diagonal-restricted external functor. -/
def leftTensorIso (F : EnrichedFunctorCat V A) :
    MonoidalCategory.tensorLeft F ≅
      PointwiseTensor.leftTensor PointwiseTensor.cartesianDiagonal F :=
  NatIso.ofComponents (fun G => Iso.refl (tensorObject F G)) (by
    intro G H q
    simp only [Iso.refl_hom]
    apply hom_ext
    intro a
    erw [component_comp, component_comp, component_id, component_id]
    simp only [Category.comp_id, Category.id_comp]
    erw [PointwiseTensor.leftTensor_map_component]
    change component (F ◁ q) a =
      𝟙 (F.toEnrichedFunctor.obj a) ⊗ₘ component q a
    apply CartesianMonoidalCategory.hom_ext
    · erw [tensorHom_fst, Category.comp_id]
      have hf : (F ◁ q) ≫ firstProjection F H = firstProjection F G := by
        change (𝟙 F ⊗ₘ q) ≫ CartesianMonoidalCategory.fst F H =
          CartesianMonoidalCategory.fst F G
        rw [CartesianMonoidalCategory.tensorHom_fst, Category.comp_id]
      have h := congrArg (fun f => component f a) hf
      rw [component_comp] at h
      erw [firstProjection_component, firstProjection_component] at h
      exact h
    · erw [tensorHom_snd]
      have hg : (F ◁ q) ≫ secondProjection F H = secondProjection F G ≫ q := by
        change (𝟙 F ⊗ₘ q) ≫ CartesianMonoidalCategory.snd F H =
          CartesianMonoidalCategory.snd F G ≫ q
        exact CartesianMonoidalCategory.tensorHom_snd (𝟙 F) q
      have h := congrArg (fun f => component f a) hg
      rw [component_comp, component_comp] at h
      erw [secondProjection_component, secondProjection_component] at h
      exact h)

variable [HasProducts.{uA} V] [HasEqualizers V]

/-- The pointwise monoidal tensor is closed by the actual original Kan/end right adjoint. -/
@[instance_reducible]
def monoidalClosed : MonoidalClosed (EnrichedFunctorCat V A) where
  closed F :=
    { rightAdj := PointwiseTensor.rightTensor PointwiseTensor.cartesianDiagonal F
      adj := (PointwiseTensor.adjunction PointwiseTensor.cartesianDiagonal F).ofNatIsoLeft
        (leftTensorIso F).symm }

/-- The constructed internal Hom retains the complete original right Kan and weighted end. -/
theorem ihom_eq (F : EnrichedFunctorCat V A) :
    letI := monoidalClosed (V := V) (A := A)
    ihom F = PointwiseTensor.rightTensor PointwiseTensor.cartesianDiagonal F := rfl

end CategoryTheory.EnrichedFunctorCat.PointwiseCartesian
