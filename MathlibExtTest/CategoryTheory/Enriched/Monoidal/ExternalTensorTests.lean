/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.Monoidal.ExternalTensor

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonoidalClosed

set_option autoImplicit false

noncomputable section

universe uC uD uV vV

section PlainIndependentIndices

attribute [local instance] CategoryTheory.Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {F₀ F₁ F₂ : EnrichedFunctor V C V}
  {G₀ G₁ G₂ : EnrichedFunctor V D V}

-- This consumes the transformation's whole product-enriched hom naturality.
example
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁) (x y : C × D) :
    MonoidalClosed.uncurry ((F₀.externalTensor G₀).map x y) ≫
        (eHomEquiv V).symm ((EnrichedFunctor.externalMap a b).app y) =
      ((eHomEquiv V).symm ((EnrichedFunctor.externalMap a b).app x) ⊗ₘ
          𝟙 (x ⟶[V] y)) ≫
        MonoidalClosed.uncurry ((F₁.externalTensor G₁).map x y) :=
  (EnrichedFunctor.externalMap a b).uncurriedNaturality x y

example
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁) (x : C × D) :
    (eHomEquiv V).symm ((EnrichedFunctor.externalMap a b).app x) =
      (eHomEquiv V).symm (a.app x.1) ⊗ₘ (eHomEquiv V).symm (b.app x.2) :=
  EnrichedFunctor.externalMap_component a b x

-- The entire external-tensor map is available from this generic import alone.
example (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (x y : C × D) :
    MonoidalClosed.uncurry ((F.externalTensor G).map x y) =
      MonoidalCategory.tensorμ (F.obj x.1) (G.obj x.2)
        (x.1 ⟶[V] y.1) (x.2 ⟶[V] y.2) ≫
        (MonoidalClosed.uncurry (F.map x.1 y.1) ⊗ₘ
          MonoidalClosed.uncurry (G.map x.2 y.2)) :=
  EnrichedFunctor.externalTensor_uncurry F G x y

example (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) :
    EnrichedFunctor.externalMap (GradedNatTrans.unitId F) (GradedNatTrans.unitId G) =
      GradedNatTrans.unitId (F.externalTensor G) :=
  EnrichedFunctor.externalMap_id F G

example
    (a₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (a₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₁ F₂)
    (b₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁)
    (b₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₁ G₂) :
    EnrichedFunctor.externalMap
        (GradedNatTrans.unitComp a₀₁ a₁₂) (GradedNatTrans.unitComp b₀₁ b₁₂) =
      GradedNatTrans.unitComp
        (EnrichedFunctor.externalMap a₀₁ b₀₁) (EnrichedFunctor.externalMap a₁₂ b₁₂) :=
  EnrichedFunctor.externalMap_comp a₀₁ a₁₂ b₀₁ b₁₂

end PlainIndependentIndices
