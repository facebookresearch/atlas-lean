/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.ExternalTensor
public import MathlibExt.CategoryTheory.Enriched.ScalarTensor

/-!
# External tensor and the actual scalar associator

The external tensor of a left-tensored enriched diagram and a second diagram
is isomorphic to the left tensor of their external tensor. Its components are
the original ambient associator and inverse. Naturality retains the full
product-enriched Hom action, both input transformations and all scalar arrows.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe uV vV uC uD

open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat

attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]

omit [MonoidalClosed V] in
private theorem scalarExternalTensorAction (M A B P Q A' B' : V)
    (f : A ⊗ P ⟶ A') (g : B ⊗ Q ⟶ B') :
    tensorμ (M ⊗ A) B P Q ≫
        (((α_ M A P).hom ≫ M ◁ f) ⊗ₘ g) ≫ (α_ M A' B').hom =
      ((α_ M A B).hom ⊗ₘ 𝟙 (P ⊗ Q)) ≫ (α_ M (A ⊗ B) (P ⊗ Q)).hom ≫
        M ◁ (tensorμ A B P Q ≫ (f ⊗ₘ g)) := by
  dsimp only [tensorμ]
  monoidal

/-- The ambient associator respects the complete original external Hom action. -/
theorem externalTensorScalar_full_naturality (M : V)
    (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (a b : C × D) :
    MonoidalClosed.uncurry (((EnrichedFunctor.tensorLeft M F).externalTensor G).map a b) ≫
        (α_ M (F.obj b.1) (G.obj b.2)).hom =
      ((α_ M (F.obj a.1) (G.obj a.2)).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((EnrichedFunctor.tensorLeft M (F.externalTensor G)).map a b) := by
  let P : V := a.1 ⟶[V] b.1
  let Q : V := a.2 ⟶[V] b.2
  let f := MonoidalClosed.uncurry (F.map a.1 b.1)
  let g := MonoidalClosed.uncurry (G.map a.2 b.2)
  have hSource :
      MonoidalClosed.uncurry (((EnrichedFunctor.tensorLeft M F).externalTensor G).map a b) =
        tensorμ (M ⊗ F.obj a.1) (G.obj a.2) P Q ≫
          (((α_ M (F.obj a.1) P).hom ≫ M ◁ f) ⊗ₘ g) :=
    (EnrichedFunctor.externalTensor_uncurry (EnrichedFunctor.tensorLeft M F) G a b).trans
      (congrArg (fun r => tensorμ (M ⊗ F.obj a.1) (G.obj a.2) P Q ≫ (r ⊗ₘ g))
        (EnrichedFunctor.tensorLeft_map_uncurry M F a.1 b.1))
  have hTarget :
      MonoidalClosed.uncurry ((EnrichedFunctor.tensorLeft M (F.externalTensor G)).map a b) =
        (α_ M (F.obj a.1 ⊗ G.obj a.2) (P ⊗ Q)).hom ≫
          M ◁ (tensorμ (F.obj a.1) (G.obj a.2) P Q ≫ (f ⊗ₘ g)) :=
    (EnrichedFunctor.tensorLeft_map_uncurry M (F.externalTensor G) a b).trans
      (congrArg
        (fun r => (α_ M (F.obj a.1 ⊗ G.obj a.2) (P ⊗ Q)).hom ≫ M ◁ r)
        (EnrichedFunctor.externalTensor_uncurry F G a b))
  exact (congrArg (fun r => r ≫ (α_ M (F.obj b.1) (G.obj b.2)).hom) hSource).trans
    ((Category.assoc _ _ _).trans
      ((scalarExternalTensorAction M _ _ P Q _ _ f g).trans
        (congrArg (fun r => ((α_ M (F.obj a.1) (G.obj a.2)).hom ⊗ₘ 𝟙 (P ⊗ Q)) ≫ r)
          hTarget.symm)))

/-- Inverse naturality is derived from the actual associator and the full forward square. -/
theorem externalTensorScalar_inv_full_naturality (M : V)
    (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (a b : C × D) :
    MonoidalClosed.uncurry ((EnrichedFunctor.tensorLeft M (F.externalTensor G)).map a b) ≫
        (α_ M (F.obj b.1) (G.obj b.2)).inv =
      ((α_ M (F.obj a.1) (G.obj a.2)).inv ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry
          (((EnrichedFunctor.tensorLeft M F).externalTensor G).map a b) := by
  let H : V := a ⟶[V] b
  let e := α_ M (F.obj a.1) (G.obj a.2)
  let e' := α_ M (F.obj b.1) (G.obj b.2)
  let f : ((M ⊗ F.obj a.1) ⊗ G.obj a.2) ⊗ H ⟶ (M ⊗ F.obj b.1) ⊗ G.obj b.2 :=
    MonoidalClosed.uncurry (((EnrichedFunctor.tensorLeft M F).externalTensor G).map a b)
  let g : (M ⊗ (F.obj a.1 ⊗ G.obj a.2)) ⊗ H ⟶ M ⊗ (F.obj b.1 ⊗ G.obj b.2) :=
    MonoidalClosed.uncurry ((EnrichedFunctor.tensorLeft M (F.externalTensor G)).map a b)
  have h : f ≫ e'.hom = (e.hom ▷ H) ≫ g :=
    (externalTensorScalar_full_naturality M F G a b).trans
      (congrArg (fun r => r ≫ g) (tensorHom_id e.hom H))
  have hInv : g ≫ e'.inv = (e.inv ▷ H) ≫ f := by
    apply (cancel_epi (e.hom ▷ H)).1
    calc
      _ = f ≫ e'.hom ≫ e'.inv :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun r => r ≫ e'.inv) h.symm).trans (Category.assoc _ _ _))
      _ = f := (congrArg (fun r => f ≫ r) e'.hom_inv_id).trans (Category.comp_id f)
      _ = _ := (hom_inv_whiskerRight_assoc e H f).symm
  exact hInv.trans (congrArg (fun r => r ≫ f) (tensorHom_id e.inv H).symm)

/-- The original associator gives a genuine forward transformation. -/
def externalTensorScalarHom (M : V)
    (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) :
    (⟨(EnrichedFunctor.tensorLeft M F).externalTensor G⟩ : EnrichedFunctorCat V (C × D)) ⟶
      tensorLeftObject M ⟨F.externalTensor G⟩ :=
  GradedNatTrans.unitOfComponents
    (fun a => (α_ M (F.obj a.1) (G.obj a.2)).hom)
    (externalTensorScalar_full_naturality M F G)

/-- The original inverse associator gives a genuine inverse transformation. -/
def externalTensorScalarInv (M : V)
    (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) :
    tensorLeftObject M ⟨F.externalTensor G⟩ ⟶
      (⟨(EnrichedFunctor.tensorLeft M F).externalTensor G⟩ : EnrichedFunctorCat V (C × D)) :=
  GradedNatTrans.unitOfComponents
    (fun a => (α_ M (F.obj a.1) (G.obj a.2)).inv)
    (externalTensorScalar_inv_full_naturality M F G)

/-- The forward transformation retains the literal ambient associator. -/
theorem externalTensorScalarHom_component (M : V)
    (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (a : C × D) :
    component (externalTensorScalarHom M F G) a =
      (α_ M (F.obj a.1) (G.obj a.2)).hom :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The inverse transformation retains the literal inverse ambient associator. -/
theorem externalTensorScalarInv_component (M : V)
    (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (a : C × D) :
    component (externalTensorScalarInv M F G) a =
      (α_ M (F.obj a.1) (G.obj a.2)).inv :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The genuine enriched external scalar comparison uses the original ambient associator. -/
def externalTensorScalarIso (M : V)
    (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) :
    (⟨(EnrichedFunctor.tensorLeft M F).externalTensor G⟩ : EnrichedFunctorCat V (C × D)) ≅
      tensorLeftObject M ⟨F.externalTensor G⟩ where
  hom := externalTensorScalarHom M F G
  inv := externalTensorScalarInv M F G
  hom_inv_id := by
    apply hom_ext
    intro a
    refine (component_comp (externalTensorScalarHom M F G)
        (externalTensorScalarInv M F G) a).trans ?_
    refine Eq.trans ?_ (component_id _ a).symm
    exact (congrArg₂ (fun r s => r ≫ s)
      (externalTensorScalarHom_component M F G a)
      (externalTensorScalarInv_component M F G a)).trans (Iso.hom_inv_id _)
  inv_hom_id := by
    apply hom_ext
    intro a
    refine (component_comp (externalTensorScalarInv M F G)
        (externalTensorScalarHom M F G) a).trans ?_
    refine Eq.trans ?_ (component_id _ a).symm
    exact (congrArg₂ (fun r s => r ≫ s)
      (externalTensorScalarInv_component M F G a)
      (externalTensorScalarHom_component M F G a)).trans (Iso.inv_hom_id _)

/-- Every forward component is the literal original ambient associator. -/
theorem externalTensorScalarIso_hom_component (M : V)
    (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (a : C × D) :
    component (externalTensorScalarIso M F G).hom a =
      (α_ M (F.obj a.1) (G.obj a.2)).hom :=
  externalTensorScalarHom_component M F G a

/-- Every inverse component is the literal original inverse ambient associator. -/
theorem externalTensorScalarIso_inv_component (M : V)
    (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (a : C × D) :
    component (externalTensorScalarIso M F G).inv a =
      (α_ M (F.obj a.1) (G.obj a.2)).inv :=
  externalTensorScalarInv_component M F G a

variable {F F' : EnrichedFunctor V C V} {G G' : EnrichedFunctor V D V}

/-- The actual comparison is natural in both complete genuine input transformations. -/
theorem externalTensorScalarIso_naturality (M : V)
    (p : (⟨F⟩ : EnrichedFunctorCat V C) ⟶ ⟨F'⟩)
    (q : (⟨G⟩ : EnrichedFunctorCat V D) ⟶ ⟨G'⟩) :
    EnrichedFunctor.externalMap (tensorLeftMap M p) q ≫
        (externalTensorScalarIso M F' G').hom =
      (externalTensorScalarIso M F G).hom ≫
        tensorLeftMap M (F := ⟨F.externalTensor G⟩) (G := ⟨F'.externalTensor G'⟩)
          (EnrichedFunctor.externalMap p q) := by
  apply hom_ext
  intro a
  have hMap := (EnrichedFunctor.externalMap_component (tensorLeftMap M p) q a).trans
    (congrArg (fun r => r ⊗ₘ component q a.2) (tensorLeftMap_component M p a.1))
  have hScalar :=
    (tensorLeftMap_component M (F := ⟨F.externalTensor G⟩) (G := ⟨F'.externalTensor G'⟩)
      (EnrichedFunctor.externalMap p q) a).trans
        (congrArg (fun r => M ◁ r) (EnrichedFunctor.externalMap_component p q a))
  have hNat : ((M ◁ component p a.1) ⊗ₘ component q a.2) ≫
      (α_ M (F'.obj a.1) (G'.obj a.2)).hom =
    (α_ M (F.obj a.1) (G.obj a.2)).hom ≫ M ◁ (component p a.1 ⊗ₘ component q a.2) := by
    simpa only [id_tensorHom] using
      associator_naturality (𝟙 M) (component p a.1) (component q a.2)
  exact (component_comp _ _ a).trans
    ((congrArg₂ (fun r s => r ≫ s) hMap
      (externalTensorScalarIso_hom_component M F' G' a)).trans
        (hNat.trans ((congrArg₂ (fun r s => r ≫ s)
          (externalTensorScalarIso_hom_component M F G a).symm hScalar.symm).trans
            (component_comp _ _ a).symm)))

/-- The actual inverse comparison is natural in both complete genuine input transformations. -/
theorem externalTensorScalarIso_inv_naturality (M : V)
    (p : (⟨F⟩ : EnrichedFunctorCat V C) ⟶ ⟨F'⟩)
    (q : (⟨G⟩ : EnrichedFunctorCat V D) ⟶ ⟨G'⟩) :
    tensorLeftMap M (F := ⟨F.externalTensor G⟩) (G := ⟨F'.externalTensor G'⟩)
        (EnrichedFunctor.externalMap p q) ≫ (externalTensorScalarIso M F' G').inv =
      (externalTensorScalarIso M F G).inv ≫
        EnrichedFunctor.externalMap (tensorLeftMap M p) q := by
  apply hom_ext
  intro a
  have hMap := (EnrichedFunctor.externalMap_component (tensorLeftMap M p) q a).trans
    (congrArg (fun r => r ⊗ₘ component q a.2) (tensorLeftMap_component M p a.1))
  have hScalar :=
    (tensorLeftMap_component M (F := ⟨F.externalTensor G⟩) (G := ⟨F'.externalTensor G'⟩)
      (EnrichedFunctor.externalMap p q) a).trans
        (congrArg (fun r => M ◁ r) (EnrichedFunctor.externalMap_component p q a))
  have hNat : (M ◁ (component p a.1 ⊗ₘ component q a.2)) ≫
      (α_ M (F'.obj a.1) (G'.obj a.2)).inv =
    (α_ M (F.obj a.1) (G.obj a.2)).inv ≫ ((M ◁ component p a.1) ⊗ₘ component q a.2) := by
    simpa only [id_tensorHom] using
      associator_inv_naturality (𝟙 M) (component p a.1) (component q a.2)
  exact (component_comp _ _ a).trans
    ((congrArg₂ (fun r s => r ≫ s) hScalar
      (externalTensorScalarIso_inv_component M F' G' a)).trans
        (hNat.trans ((congrArg₂ (fun r s => r ≫ s)
          (externalTensorScalarIso_inv_component M F G a).symm hMap.symm).trans
            (component_comp _ _ a).symm)))

/-- The original associator is natural in every scalar arrow. -/
theorem externalTensorScalarIso_scalar_naturality {M N : V} (h : M ⟶ N)
    (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) :
    EnrichedFunctor.externalMap (scalarTensorMap h ⟨F⟩)
        (𝟙 (⟨G⟩ : EnrichedFunctorCat V D)) ≫ (externalTensorScalarIso N F G).hom =
      (externalTensorScalarIso M F G).hom ≫ scalarTensorMap h ⟨F.externalTensor G⟩ := by
  apply hom_ext
  intro a
  have hMap := (EnrichedFunctor.externalMap_component (scalarTensorMap h ⟨F⟩)
    (𝟙 (⟨G⟩ : EnrichedFunctorCat V D)) a).trans
      ((congrArg₂ (fun r s => r ⊗ₘ s) (scalarTensorMap_component h ⟨F⟩ a.1)
        (component_id (⟨G⟩ : EnrichedFunctorCat V D) a.2)).trans
          (tensorHom_id (h ▷ F.obj a.1) (G.obj a.2)))
  exact (component_comp _ _ a).trans
    ((congrArg₂ (fun r s => r ≫ s) hMap
      (externalTensorScalarIso_hom_component N F G a)).trans
        ((associator_naturality_left h (F.obj a.1) (G.obj a.2)).trans
          ((congrArg₂ (fun r s => r ≫ s)
            (externalTensorScalarIso_hom_component M F G a).symm
            (scalarTensorMap_component h ⟨F.externalTensor G⟩ a).symm).trans
              (component_comp _ _ a).symm)))

/-- The original inverse associator is natural in every scalar arrow. -/
theorem externalTensorScalarIso_inv_scalar_naturality {M N : V} (h : M ⟶ N)
    (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) :
    scalarTensorMap h ⟨F.externalTensor G⟩ ≫ (externalTensorScalarIso N F G).inv =
      (externalTensorScalarIso M F G).inv ≫
        EnrichedFunctor.externalMap (scalarTensorMap h ⟨F⟩)
          (𝟙 (⟨G⟩ : EnrichedFunctorCat V D)) := by
  apply hom_ext
  intro a
  have hMap := (EnrichedFunctor.externalMap_component (scalarTensorMap h ⟨F⟩)
    (𝟙 (⟨G⟩ : EnrichedFunctorCat V D)) a).trans
      ((congrArg₂ (fun r s => r ⊗ₘ s) (scalarTensorMap_component h ⟨F⟩ a.1)
        (component_id (⟨G⟩ : EnrichedFunctorCat V D) a.2)).trans
          (tensorHom_id (h ▷ F.obj a.1) (G.obj a.2)))
  exact (component_comp _ _ a).trans
    ((congrArg₂ (fun r s => r ≫ s) (scalarTensorMap_component h ⟨F.externalTensor G⟩ a)
      (externalTensorScalarIso_inv_component N F G a)).trans
        ((associator_inv_naturality_left h (F.obj a.1) (G.obj a.2)).trans
          ((congrArg₂ (fun r s => r ≫ s)
            (externalTensorScalarIso_inv_component M F G a).symm hMap.symm).trans
              (component_comp _ _ a).symm)))

end CategoryTheory.EnrichedFunctorCat
