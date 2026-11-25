/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.ExternalTensorMappingEndAdjunction
public import MathlibExt.CategoryTheory.Enriched.RightKanExtension
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Pointwise tensors on genuine enriched diagrams

An enriched diagonal is source data: it acts on the entire index Hom object.
The pointwise left tensor is its literal restriction of the external tensor.
The right adjoint uses the actual enriched right Kan end and then the original
external mapping end. A cartesian coefficient category supplies a canonical
compatible diagonal without changing the original enriched index.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe uA uV vV

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.PointwiseTensor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

attribute [local instance] Enriched.prodCategory

/-- The pointwise tensor keeps the caller's actual enriched diagonal. -/
def leftTensor (δ : EnrichedFunctor V A (A × A)) (F : EnrichedFunctorCat V A) :
    EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V A :=
  ExternalTensorMappingEndAdjunction.leftFunctor F ⋙ restriction δ

/-- The literal value retains both original factors at the diagonal's original object. -/
theorem leftTensor_obj (δ : EnrichedFunctor V A (A × A)) (F G : EnrichedFunctorCat V A)
    (a : A) :
    ((leftTensor δ F).obj G).toEnrichedFunctor.obj a =
      F.toEnrichedFunctor.obj (δ.obj a).1 ⊗ G.toEnrichedFunctor.obj (δ.obj a).2 := rfl

/-- The action retains the complete original diagonal Hom map before the external action. -/
theorem leftTensor_fullHom (δ : EnrichedFunctor V A (A × A)) (F G : EnrichedFunctorCat V A)
    (a b : A) :
    ((leftTensor δ F).obj G).toEnrichedFunctor.map a b =
      δ.map a b ≫ (F.toEnrichedFunctor.externalTensor G.toEnrichedFunctor).map
        (δ.obj a) (δ.obj b) := rfl

/-- The entire input transformation is tensored through its actual original component. -/
theorem leftTensor_map_component (δ : EnrichedFunctor V A (A × A))
    (F : EnrichedFunctorCat V A) {G H : EnrichedFunctorCat V A} (q : G ⟶ H) (a : A) :
    component ((leftTensor δ F).map q) a =
      𝟙 (F.toEnrichedFunctor.obj (δ.obj a).1) ⊗ₘ component q (δ.obj a).2 := by
  change component (restrictionMap δ
    ((ExternalTensorMappingEndAdjunction.leftFunctor F).map q)) a = _
  rw [restrictionMap_component]
  exact ExternalTensorMappingEndAdjunction.leftFunctor_map_component F q (δ.obj a).1 (δ.obj a).2

variable [HasProducts.{uA} V] [HasEqualizers V]

/-- The right adjoint is the genuine Kan-end/external-end composite for the same δ. -/
def rightTensor (δ : EnrichedFunctor V A (A × A)) (F : EnrichedFunctorCat V A) :
    EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V A :=
  rightKan δ ⋙ ExternalTensorMappingEndAdjunction.rightFunctor F

/-- The actual right-Hom value is the weighted end on the original right-Kan slice. -/
theorem rightTensor_obj (δ : EnrichedFunctor V A (A × A)) (F G : EnrichedFunctorCat V A)
    (a : A) :
    ((rightTensor δ F).obj G).toEnrichedFunctor.obj a =
      ExternalTensorMappingEndAdjunction.mappingObject F ((rightKan δ).obj G) a := rfl

/-- Compose the two existing full checked adjunctions, retaining all original functor maps. -/
def adjunction (δ : EnrichedFunctor V A (A × A)) (F : EnrichedFunctorCat V A) :
    leftTensor δ F ⊣ rightTensor δ F :=
  (ExternalTensorMappingEndAdjunction.adjunction F).comp (rightKanAdjunction δ)

set_option backward.isDefEq.respectTransparency false in
/-- The complete transpose is the original Kan transpose followed by the original end transpose. -/
theorem adjunction_homEquiv (δ : EnrichedFunctor V A (A × A))
    (F G H : EnrichedFunctorCat V A) (q : (leftTensor δ F).obj G ⟶ H) :
    (adjunction δ F).homEquiv G H q =
      (ExternalTensorMappingEndAdjunction.adjunction F).homEquiv G ((rightKan δ).obj H)
        ((rightKanAdjunction δ).homEquiv
          ((ExternalTensorMappingEndAdjunction.leftFunctor F).obj G) H q) := by
  dsimp only [adjunction, leftTensor, rightTensor]
  rw [Adjunction.comp_homEquiv]
  rfl

end CategoryTheory.EnrichedFunctorCat.PointwiseTensor

namespace CategoryTheory.EnrichedFunctorCat.PointwiseTensor

open CartesianMonoidalCategory

variable {V : Type uV} [Category.{vV} V] [CartesianMonoidalCategory V]
  [SymmetricCategory V] {A : Type uA} [EnrichedCategory V A]

attribute [local instance] Enriched.prodCategory

set_option backward.isDefEq.respectTransparency false in
/-- Cartesian Hom objects supply the actual enriched diagonal for an arbitrary A. -/
def cartesianDiagonal : EnrichedFunctor V A (A × A) where
  obj a := (a, a)
  map a b := lift (𝟙 (a ⟶[V] b)) (𝟙 (a ⟶[V] b))
  map_id a := by
    change eId V a ≫ lift (𝟙 (a ⟶[V] a)) (𝟙 (a ⟶[V] a)) =
      (λ_ (𝟙_ V)).inv ≫ (eId V a ⊗ₘ eId V a)
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst, Category.comp_id]
      rw [← rightUnitor_hom (𝟙_ V), ← unitors_equal, Iso.inv_hom_id_assoc]
    · simp only [Category.assoc, lift_snd, tensorHom_snd, Category.comp_id]
      rw [← leftUnitor_hom (𝟙_ V), Iso.inv_hom_id_assoc]
  map_comp a b c := by
    change eComp V a b c ≫ lift (𝟙 (a ⟶[V] c)) (𝟙 (a ⟶[V] c)) =
      (lift (𝟙 (a ⟶[V] b)) (𝟙 (a ⟶[V] b)) ⊗ₘ
        lift (𝟙 (b ⟶[V] c)) (𝟙 (b ⟶[V] c))) ≫
        tensorμ (a ⟶[V] b) (a ⟶[V] b) (b ⟶[V] c) (b ⟶[V] c) ≫
          (eComp V a b c ⊗ₘ eComp V a b c)
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst]
      rw [← Category.assoc _ _ (eComp V a b c), tensorμ_fst,
        tensorHom_comp_tensorHom_assoc]
      simp only [lift_fst, id_tensorHom_id, Category.id_comp, Category.comp_id]
    · simp only [Category.assoc, lift_snd, tensorHom_snd]
      rw [← Category.assoc _ _ (eComp V a b c), tensorμ_snd,
        tensorHom_comp_tensorHom_assoc]
      simp only [lift_snd, id_tensorHom_id, Category.id_comp, Category.comp_id]

/-- The canonical diagonal keeps each original index object unchanged. -/
theorem cartesianDiagonal_obj (a : A) :
    (cartesianDiagonal (V := V)).obj a = (a, a) := rfl

/-- The actual complete diagonal Hom map is the chosen coefficient product lift. -/
theorem cartesianDiagonal_map (a b : A) :
    (cartesianDiagonal (V := V)).map a b =
      lift (𝟙 (a ⟶[V] b)) (𝟙 (a ⟶[V] b)) := rfl

/-- Both original Hom projections of the cartesian diagonal are identities. -/
theorem cartesianDiagonal_fst (a b : A) :
    (cartesianDiagonal (V := V)).map a b ≫ fst (a ⟶[V] b) (a ⟶[V] b) =
      𝟙 (a ⟶[V] b) := lift_fst _ _

/-- The other complete Hom projection is the same original identity. -/
theorem cartesianDiagonal_snd (a b : A) :
    (cartesianDiagonal (V := V)).map a b ≫ snd (a ⟶[V] b) (a ⟶[V] b) =
      𝟙 (a ⟶[V] b) := lift_snd _ _

end CategoryTheory.EnrichedFunctorCat.PointwiseTensor
