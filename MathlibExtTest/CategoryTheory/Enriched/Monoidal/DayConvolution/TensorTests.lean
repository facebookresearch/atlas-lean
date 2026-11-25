/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Tensor

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonoidalClosed

set_option autoImplicit false

noncomputable section

universe uC uD uK uV vV

section PlainIndependentIndices

attribute [local instance] CategoryTheory.Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  {F₀ F₁ F₂ : EnrichedFunctor V C V}
  {G₀ G₁ G₂ : EnrichedFunctor V D V}

-- Only one particular kernel is available in this identity client.
example (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K)
    [HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)] :
    EnrichedDayKernel.Input.mapAt T (GradedNatTrans.unitId F) (GradedNatTrans.unitId G) k =
      𝟙 (EnrichedDayKernel.obj T F G k) :=
  EnrichedDayKernel.Input.mapAt_id T F G k

-- Exactly three kernels at this one k are available for composition.
example
    (a₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (a₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₁ F₂)
    (b₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁)
    (b₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₁ G₂) (k : K)
    [HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k)
      (EnrichedDayKernel.rightMap T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k)
      (EnrichedDayKernel.rightMap T F₁ G₁ k)]
    [HasCoproduct (EnrichedDayKernel.relations T F₂ G₂ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₂ G₂ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₂ G₂ k)
      (EnrichedDayKernel.rightMap T F₂ G₂ k)] :
    EnrichedDayKernel.Input.mapAt T
        (GradedNatTrans.unitComp a₀₁ a₁₂) (GradedNatTrans.unitComp b₀₁ b₁₂) k =
      EnrichedDayKernel.Input.mapAt T a₀₁ b₀₁ k ≫
        EnrichedDayKernel.Input.mapAt T a₁₂ b₁₂ k :=
  EnrichedDayKernel.Input.mapAt_comp T a₀₁ a₁₂ b₀₁ b₁₂ k

-- Only the four actual endpoint kernels are available for the full hom square.
example
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁) (k k' : K)
    [HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k)
      (EnrichedDayKernel.rightMap T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k')]
    [HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k')
      (EnrichedDayKernel.rightMap T F₀ G₀ k')]
    [HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k)
      (EnrichedDayKernel.rightMap T F₁ G₁ k)]
    [HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k')]
    [HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k')
      (EnrichedDayKernel.rightMap T F₁ G₁ k')] :
    MonoidalClosed.uncurry (EnrichedDayKernel.Output.map T F₀ G₀ k k') ≫
        EnrichedDayKernel.Input.mapAt T a b k' =
      (EnrichedDayKernel.Input.mapAt T a b k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫
        MonoidalClosed.uncurry (EnrichedDayKernel.Output.map T F₁ G₁ k k') :=
  EnrichedDayKernel.Input.mapAt_natural T a b k k'

example
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁)
    [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k)]
    [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k)
      (EnrichedDayKernel.rightMap T F₀ G₀ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k)]
    [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k)
      (EnrichedDayKernel.rightMap T F₁ G₁ k)] :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (EnrichedDayKernel.Output.functor T F₀ G₀)
      (EnrichedDayKernel.Output.functor T F₁ G₁) :=
  EnrichedDayKernel.Input.natTrans T a b

end PlainIndependentIndices

section WholeInputCategories

attribute [local instance] CategoryTheory.Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
    HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
    HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
    HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)]

example (X : EnrichedFunctorCat V C × EnrichedFunctorCat V D) :
    (EnrichedDayKernel.Input.bifunctor T).map (𝟙 X) =
      𝟙 ((EnrichedDayKernel.Input.bifunctor T).obj X) :=
  (EnrichedDayKernel.Input.bifunctor T).map_id X

example {X Y Z : EnrichedFunctorCat V C × EnrichedFunctorCat V D}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    (EnrichedDayKernel.Input.bifunctor T).map (a ≫ b) =
      (EnrichedDayKernel.Input.bifunctor T).map a ≫ (EnrichedDayKernel.Input.bifunctor T).map b :=
  (EnrichedDayKernel.Input.bifunctor T).map_comp a b

example {F F' : EnrichedFunctorCat V C} {G G' : EnrichedFunctorCat V D}
    (a : F ⟶ F') (b : G ⟶ G') (k : K) :
    EnrichedFunctorCat.component
        (F := ⟨EnrichedDayKernel.Output.functor T F.toEnrichedFunctor G.toEnrichedFunctor⟩)
        (G := ⟨EnrichedDayKernel.Output.functor T F'.toEnrichedFunctor G'.toEnrichedFunctor⟩)
        ((EnrichedDayKernel.Input.bifunctor T).map (X := (F, G)) (Y := (F', G')) (a, b)) k =
      EnrichedDayKernel.Input.mapAt T
        (F₀ := F.toEnrichedFunctor) (F₁ := F'.toEnrichedFunctor)
        (G₀ := G.toEnrichedFunctor) (G₁ := G'.toEnrichedFunctor) a b k :=
  EnrichedDayKernel.Input.bifunctor_map_component T
    (F := F) (F' := F') (G := G) (G' := G') a b k

end WholeInputCategories
