/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialSet.FilteredColimitStageData
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SSet.FilteredColimitStage.Test
private theorem original_filtered_arbitrary_category
    {J : Type v} [Category.{w} J] [Small.{u} J] [IsFiltered J]
    {F : J ⥤ SSet.{u}} (c : Cocone F) (hc : IsColimit c)
    (hm : ∀ ⦃i j : J⦄ (f : i ⟶ j), Mono (F.map f)) (j : J) : Mono (c.ι.app j) :=
  cocone_legs_mono_of_maps_mono c hc hm j
private theorem original_whole_simplex_before_operator
    {J : Type v} [Category.{w} J] [Small.{u} J]
    {F : J ⥤ SSet.{u}} (c : Cocone F) (hc : IsColimit c)
    (n : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ c.pt) :
    ∃ (j : J) (bj : (Δ[n] : SSet.{u}) ⟶ F.obj j),
      bj ≫ c.ι.app j = b ∧
        ∀ (m : ℕ) (delta : ⦋m⦌ ⟶ ⦋n⦌),
          (SSet.stdSimplex.map delta ≫ bj) ≫ c.ι.app j = SSet.stdSimplex.map delta ≫ b :=
  exists_simplex_stage_with_all_operators c hc n b
end SSet.FilteredColimitStage.Test
