/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStage

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v uD vD
open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.IteratedStageFlattenNaturality
open CategoryTheory.Waldhausen.SConstruction
variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type (max uD vD)} [Category.{vD} D] [HasZeroObject D]
    [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- No outer stages leaves the complete original inner carrier unchanged. -/
theorem originalNilFlatten (ms : List ℕ) :
    (iteratedStageFlattenEquivalence C [] ms).functor =
      (iteratedStageNilEquivalence (IteratedStage C ms)).functor :=
  iteratedStageFlattenEquivalence_nil C ms

/-- Every original inner exact map commutes with its complete nil flattening chart. -/
theorem originalNilMapSquare (ms : List ℕ) :
    mapIteratedStage (mapIteratedStage_isWaldhausenExact hF ms) [] ⋙
        (iteratedStageFlattenEquivalence D [] ms).functor =
      (iteratedStageFlattenEquivalence C [] ms).functor ⋙ mapIteratedStage hF ms :=
  iteratedStageFlattenEquivalence_map_nil C hF ms

/-- The full original nested and flattened exact functors agree in every degree list. -/
theorem originalFullMapSquare (ns ms : List ℕ) :
    mapIteratedStage (mapIteratedStage_isWaldhausenExact hF ms) ns ⋙
        (iteratedStageFlattenEquivalence D ns ms).functor =
      (iteratedStageFlattenEquivalence C ns ms).functor ⋙
        mapIteratedStage hF (ns ++ ms) :=
  iteratedStageFlattenEquivalence_map C hF ns ms

end MathlibExtTest.IteratedStageFlattenNaturality
