/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import
  MathlibExt.Topology.Category.TopCat.Colimits.FilteredClosedColimit
public import
  MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1Embedding
public import
  MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedTransfiniteColimit
public import
 MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedSequentialPreserves
/-!
# `toSSet` keeps closed-T1 transfinite colimits

For `J`-chains in `closedT1Embeddings` with `J` linear and bottomed,
each singular simplex factors through a stage
(`toSSet_stage_exists_transfinite`), while each colimit leg stays
injective. Hence the pointwise cocone in `Type` is a colimit, and
`evaluation` reflection gives the `SSet` colimit.
Base `cdabb67f56d5cdbde9b364cf71b9125cc88234b4`.
Scope is exactly `J` diagrams in `TopCat.{u}` with all maps in
`closedT1Embeddings`; no global `PreservesColimitsOfShape` is claimed.
`IsFiltered J` is inferred from `LinearOrder`/`OrderBot`, so no extra
filter hypothesis is exposed.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Topology

namespace TopCat

variable {J : Type v} [LinearOrder J] [OrderBot J]

theorem injective_toSSet_leg_app_of_closedT1_transfinite
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), closedT1Embeddings (F.map f))
    (j : J) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((toSSet.map (c.ι.app j)).app n) := by
  have : Nonempty J := ⟨⊥⟩
  apply injective_toSSet_map_app_of_injective
  have hFclosed : ∀ ⦃i k : J⦄ (f : i ⟶ k),
      IsClosedEmbedding (F.map f).hom :=
    fun _ _ f => closedT1Embeddings_le_isClosedEmbedding _ (hF f)
  have hLeg : IsClosedEmbedding (c.ι.app j).hom :=
    isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding c hc hFclosed j
  exact hLeg.injective

theorem preservesColimit_comp_evaluation_of_closedT1_transfinite
    {F : J ⥤ TopCat.{u}}
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), closedT1Embeddings (F.map f))
    (n : SimplexCategoryᵒᵖ) :
    PreservesColimit F
      (toSSet ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n) := by
  have : Nonempty J := ⟨⊥⟩
  constructor
  intro c hc
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?hsurj ?hinj⟩
  case hsurj =>
    intro x
    obtain ⟨j, y, hy⟩ := toSSet_stage_exists_transfinite c hc hF n x
    exact ⟨j, y, by simpa using hy.symm⟩
  case hinj =>
    intro i x y hxy
    have hInj :
        Function.Injective
          (((toSSet ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n).mapCocone
            c).ι.app i) := by
      have hSSet :=
        injective_toSSet_leg_app_of_closedT1_transfinite c hc hF i n
      simpa using hSSet
    have hEq : x = y := hInj hxy
    exact ⟨i, 𝟙 i, by simpa using hEq⟩

theorem preservesColimit_toSSet_of_closedT1_transfinite
    {F : J ⥤ TopCat.{u}}
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), closedT1Embeddings (F.map f)) :
    PreservesColimit F toSSet :=
  preservesColimit_of_evaluation _ _ fun n =>
    preservesColimit_comp_evaluation_of_closedT1_transfinite hF n

end TopCat
