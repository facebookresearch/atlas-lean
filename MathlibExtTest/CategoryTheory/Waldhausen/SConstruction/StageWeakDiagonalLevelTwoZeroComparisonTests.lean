/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelTwoZeroComparison

/-!
# Diagonal degree-two zero-comparison consumer tests

Focused public-API checks for `levelTwoZeroComparisonSimplex` faces and
`levelTwoZeroComparisonCompStruct`: `δ₂` is the `G`-mapped `F` zero edge,
`δ₀` is the `G` zero edge, and `δ₁` is the `(F ⋙ G)` zero edge, plus one
packaged `SSet.Edge.CompStruct` consumer. Diagonal `2`-simplex data via
`(stageWeakDiagonal E)` only, distinguishing from the old level-one
`(stageWeakNerve E)` triangle. No duplicate proof internals.

Nonclaims: no realization, K-space law, strict functoriality, additivity, or `π₀`.
-/

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.Waldhausen.SConstruction

open scoped Simplicial

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalLevelTwoZeroComparisonTests

variable (C : Type u) [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u) [Category.{v} D] [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (E : Type u) [Category.{v} E] [Preadditive E] [Limits.HasZeroObject E]
  [HasBinaryBiproducts E] [ExactCategory E]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]
variable (G : D ⥤ E) [G.Additive] [Functor.IsExact G]

local instance : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
local instance : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E

/-- Second diagonal face is the `G`-mapped `F` zero edge.

Protects against a wrong-face (`δ₀`/`δ₁`) assignment that keeps the right
2-simplex but reads the wrong 1-face. -/
example :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (stageWeakDiagonal E).δ 2 (levelTwoZeroComparisonSimplex C D F E G) =
        (stageWeakDiagonalMapLevelZeroEdge C D F E G).edge) :=
  levelTwoZeroComparison_d2 C D F E G

/-- Zeroth diagonal face is the `G` zero edge.

Protects against swapping the `G` leg with the mapped or composite leg. -/
example :
    (letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (stageWeakDiagonal E).δ 0 (levelTwoZeroComparisonSimplex C D F E G) =
        (stageWeakDiagonalLevelZeroEdge D E G).edge) :=
  levelTwoZeroComparison_d0 C D F E G

/-- First diagonal face is the composite zero edge.

Protects against a composition-order slip where the triangle closes on the
wrong composite edge. -/
example :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      (stageWeakDiagonal E).δ 1 (levelTwoZeroComparisonSimplex C D F E G) =
        (stageWeakDiagonalLevelZeroEdge C E (F ⋙ G)).edge) :=
  levelTwoZeroComparison_d1 C D F E G

/-- Comparison triangle as bundled `CompStruct` data.

Protects against an orientation slip that provides the right 2-simplex with
the three edges in the wrong order. -/
noncomputable example :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      SSet.Edge.CompStruct
        (stageWeakDiagonalMapLevelZeroEdge C D F E G)
        (stageWeakDiagonalLevelZeroEdge D E G)
        (stageWeakDiagonalLevelZeroEdge C E (F ⋙ G))) :=
  levelTwoZeroComparisonCompStruct C D F E G

end StageWeakDiagonalLevelTwoZeroComparisonTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
