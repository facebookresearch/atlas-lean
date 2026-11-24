/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic
public import MathlibExt.CategoryTheory.Enriched.NaturalTransformation

/-!
# External tensors of genuine enriched transformations

The external tensor of enriched functors acts on full unit-graded transformations.
Its ordinary components tensor the two supplied components, and its naturality
uses the entire hom object of the product enrichment.

The generic external-tensor construction and unit-transformation support are
intentional public imports. The source categories are plain enriched categories.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC uD uV vV

namespace CategoryTheory.EnrichedFunctor

open MonoidalCategory BraidedCategory
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]

attribute [local instance] Enriched.prodCategory

/-- The entire external-tensor hom action is the tensor of the uncurried actions. -/
theorem externalTensor_uncurry (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)
    (x y : C × D) :
    MonoidalClosed.uncurry ((F.externalTensor G).map x y) =
      MonoidalCategory.tensorμ (F.obj x.1) (G.obj x.2)
        (x.1 ⟶[V] y.1) (x.2 ⟶[V] y.2) ≫
        (MonoidalClosed.uncurry (F.map x.1 y.1) ⊗ₘ
          MonoidalClosed.uncurry (G.map x.2 y.2)) := by
  rw [EnrichedFunctor.externalTensor_map]
  change
    MonoidalClosed.uncurry
        ((F.map x.1 y.1 ⊗ₘ G.map x.2 y.2) ≫
          (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
            (F.obj x.1) (F.obj y.1) (G.obj x.2) (G.obj y.2)) = _
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.enrichedMonoidalCategoryDataSelf_tensorMap,
    MonoidalClosed.uncurry_curry]
  rw [MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq]
  have ht := MonoidalCategory.tensorμ_natural_right_assoc
    (F.obj x.1) (G.obj x.2) (F.map x.1 y.1) (G.map x.2 y.2)
    ((ihom.ev (F.obj x.1)).app (F.obj y.1) ⊗ₘ
      (ihom.ev (G.obj x.2)).app (G.obj y.2))
  calc
    _ = MonoidalCategory.tensorμ (F.obj x.1) (G.obj x.2)
          (x.1 ⟶[V] y.1) (x.2 ⟶[V] y.2) ≫
        ((F.obj x.1 ◁ F.map x.1 y.1 ⊗ₘ G.obj x.2 ◁ G.map x.2 y.2) ≫
          ((ihom.ev (F.obj x.1)).app (F.obj y.1) ⊗ₘ
            (ihom.ev (G.obj x.2)).app (G.obj y.2))) := ht
    _ = _ := by rw [tensorHom_comp_tensorHom]

variable {F₀ F₁ F₂ : EnrichedFunctor V C V}
  {G₀ G₁ G₂ : EnrichedFunctor V D V}

/-- Genuine input transformations satisfy the entire product-hom naturality equation. -/
theorem externalMap_natural
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁)
    (x y : C × D) :
    MonoidalClosed.uncurry ((F₀.externalTensor G₀).map x y) ≫
        ((eHomEquiv V).symm (a.app y.1) ⊗ₘ (eHomEquiv V).symm (b.app y.2)) =
      (((eHomEquiv V).symm (a.app x.1) ⊗ₘ (eHomEquiv V).symm (b.app x.2)) ⊗ₘ
          𝟙 (x ⟶[V] y)) ≫
        MonoidalClosed.uncurry ((F₁.externalTensor G₁).map x y) := by
  let aX : F₀.obj x.1 ⟶ F₁.obj x.1 := (eHomEquiv V).symm (a.app x.1)
  let aY : F₀.obj y.1 ⟶ F₁.obj y.1 := (eHomEquiv V).symm (a.app y.1)
  let bX : G₀.obj x.2 ⟶ G₁.obj x.2 := (eHomEquiv V).symm (b.app x.2)
  let bY : G₀.obj y.2 ⟶ G₁.obj y.2 := (eHomEquiv V).symm (b.app y.2)
  have ha : MonoidalClosed.uncurry (F₀.map x.1 y.1) ≫ aY =
      (aX ⊗ₘ 𝟙 (x.1 ⟶[V] y.1)) ≫ MonoidalClosed.uncurry (F₁.map x.1 y.1) :=
    a.uncurriedNaturality x.1 y.1
  have hb : MonoidalClosed.uncurry (G₀.map x.2 y.2) ≫ bY =
      (bX ⊗ₘ 𝟙 (x.2 ⟶[V] y.2)) ≫ MonoidalClosed.uncurry (G₁.map x.2 y.2) :=
    b.uncurriedNaturality x.2 y.2
  change MonoidalClosed.uncurry ((F₀.externalTensor G₀).map x y) ≫ (aY ⊗ₘ bY) =
    ((aX ⊗ₘ bX) ⊗ₘ 𝟙 ((x.1 ⟶[V] y.1) ⊗ (x.2 ⟶[V] y.2))) ≫
      MonoidalClosed.uncurry ((F₁.externalTensor G₁).map x y)
  calc
    _ = (MonoidalCategory.tensorμ (F₀.obj x.1) (G₀.obj x.2)
          (x.1 ⟶[V] y.1) (x.2 ⟶[V] y.2) ≫
        (MonoidalClosed.uncurry (F₀.map x.1 y.1) ⊗ₘ
          MonoidalClosed.uncurry (G₀.map x.2 y.2))) ≫ (aY ⊗ₘ bY) :=
      congrArg (fun q => q ≫ (aY ⊗ₘ bY)) (externalTensor_uncurry F₀ G₀ x y)
    _ = MonoidalCategory.tensorμ (F₀.obj x.1) (G₀.obj x.2)
          (x.1 ⟶[V] y.1) (x.2 ⟶[V] y.2) ≫
        (((aX ⊗ₘ 𝟙 (x.1 ⟶[V] y.1)) ≫ MonoidalClosed.uncurry (F₁.map x.1 y.1)) ⊗ₘ
          ((bX ⊗ₘ 𝟙 (x.2 ⟶[V] y.2)) ≫ MonoidalClosed.uncurry (G₁.map x.2 y.2))) := by
      rw [Category.assoc, tensorHom_comp_tensorHom, ha, hb]
    _ = ((aX ⊗ₘ bX) ⊗ₘ 𝟙 ((x.1 ⟶[V] y.1) ⊗ (x.2 ⟶[V] y.2))) ≫
        (MonoidalCategory.tensorμ (F₁.obj x.1) (G₁.obj x.2)
            (x.1 ⟶[V] y.1) (x.2 ⟶[V] y.2) ≫
          (MonoidalClosed.uncurry (F₁.map x.1 y.1) ⊗ₘ
            MonoidalClosed.uncurry (G₁.map x.2 y.2))) := by
      rw [← tensorHom_comp_tensorHom]
      have ht := MonoidalCategory.tensorμ_natural_left_assoc aX bX
        (x.1 ⟶[V] y.1) (x.2 ⟶[V] y.2)
        (MonoidalClosed.uncurry (F₁.map x.1 y.1) ⊗ₘ
          MonoidalClosed.uncurry (G₁.map x.2 y.2))
      simpa only [tensorHom_id] using ht.symm
    _ = _ := congrArg
      (fun q => ((aX ⊗ₘ bX) ⊗ₘ 𝟙 ((x.1 ⟶[V] y.1) ⊗ (x.2 ⟶[V] y.2))) ≫ q)
      (externalTensor_uncurry F₁ G₁ x y).symm

/-- The external tensor of genuine unit-graded transformations. -/
abbrev externalMap
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (F₀.externalTensor G₀) (F₁.externalTensor G₁) :=
  GradedNatTrans.unitOfComponents
    (fun x => (eHomEquiv V).symm (a.app x.1) ⊗ₘ (eHomEquiv V).symm (b.app x.2))
    (externalMap_natural a b)

/-- The selected ordinary components of the genuine external tensor. -/
@[simp]
theorem externalMap_component
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁) (x : C × D) :
    (eHomEquiv V).symm ((externalMap a b).app x) =
      (eHomEquiv V).symm (a.app x.1) ⊗ₘ (eHomEquiv V).symm (b.app x.2) :=
  GradedNatTrans.unitOfComponents_component _ _ x

/-- Genuine external tensor preserves both input identities. -/
theorem externalMap_id (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) :
    externalMap (GradedNatTrans.unitId F) (GradedNatTrans.unitId G) =
      GradedNatTrans.unitId (F.externalTensor G) := by
  apply GradedNatTrans.ext
  funext x
  apply (eHomEquiv V).symm.injective
  let m : (F.obj x.1 ⊗ G.obj x.2) ⟶ (F.obj x.1 ⊗ G.obj x.2) :=
    (eHomEquiv V).symm ((externalMap (GradedNatTrans.unitId F) (GradedNatTrans.unitId G)).app x)
  let n : (F.obj x.1 ⊗ G.obj x.2) ⟶ (F.obj x.1 ⊗ G.obj x.2) :=
    (eHomEquiv V).symm ((GradedNatTrans.unitId (F.externalTensor G)).app x)
  have hmComponent : m =
      (eHomEquiv V).symm ((GradedNatTrans.unitId F).app x.1) ⊗ₘ
        (eHomEquiv V).symm ((GradedNatTrans.unitId G).app x.2) :=
    externalMap_component (GradedNatTrans.unitId F) (GradedNatTrans.unitId G) x
  have hF : (eHomEquiv V).symm ((GradedNatTrans.unitId F).app x.1) = 𝟙 (F.obj x.1) :=
    GradedNatTrans.unitId_component F x.1
  have hG : (eHomEquiv V).symm ((GradedNatTrans.unitId G).app x.2) = 𝟙 (G.obj x.2) :=
    GradedNatTrans.unitId_component G x.2
  have hTensor :
      (eHomEquiv V).symm ((GradedNatTrans.unitId F).app x.1) ⊗ₘ
          (eHomEquiv V).symm ((GradedNatTrans.unitId G).app x.2) =
        𝟙 (F.obj x.1 ⊗ G.obj x.2) :=
    (congrArg₂ (fun (f : F.obj x.1 ⟶ F.obj x.1) (g : G.obj x.2 ⟶ G.obj x.2) => f ⊗ₘ g)
      hF hG).trans (id_tensorHom_id _ _)
  have hm : m = 𝟙 (F.obj x.1 ⊗ G.obj x.2) := hmComponent.trans hTensor
  have hn : n = 𝟙 (F.obj x.1 ⊗ G.obj x.2) :=
    GradedNatTrans.unitId_component (F.externalTensor G) x
  change m = n
  exact hm.trans hn.symm

/-- Genuine external tensor preserves source-first input composition. -/
theorem externalMap_comp
    (a₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (a₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₁ F₂)
    (b₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁)
    (b₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₁ G₂) :
    externalMap (GradedNatTrans.unitComp a₀₁ a₁₂) (GradedNatTrans.unitComp b₀₁ b₁₂) =
      GradedNatTrans.unitComp (externalMap a₀₁ b₀₁) (externalMap a₁₂ b₁₂) := by
  apply GradedNatTrans.ext
  funext x
  apply (eHomEquiv V).symm.injective
  simp only [externalMap_component, GradedNatTrans.unitComp_component]
  exact (tensorHom_comp_tensorHom
    ((eHomEquiv V).symm (a₀₁.app x.1)) ((eHomEquiv V).symm (b₀₁.app x.2))
    ((eHomEquiv V).symm (a₁₂.app x.1)) ((eHomEquiv V).symm (b₁₂.app x.2))).symm

end CategoryTheory.EnrichedFunctor
