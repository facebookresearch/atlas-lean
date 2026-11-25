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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroEdge

/-!
# Weak-stage diagonal level-zero edge consumer tests

Focused public-API checks for `stageWeakDiagonalLevelZeroEdge`: edge
type/orientation from the mapped zero to the target zero, the identity-simplex
formula via `stageWeakDiagonalLevelZeroEdge_edge`, endpoint laws via
`stageWeakDiagonalLevelZeroEdge_src`/`stageWeakDiagonalLevelZeroEdge_tgt`, and
the two diagonal-object boundary values. Simplicial edge data only.

Nonclaims: no realization, paths, pointed maps, additivity, π₀/K₀, G-theory,
spectra, or Q/S comparison.
-/

open CategoryTheory Limits Opposite Simplicial ZeroObject
open CategoryTheory.Waldhausen.SConstruction

open scoped Simplicial

universe v₁ u₁ v₂ u₂

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroEdgeTests

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

local instance : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D

/-- Edge runs from the mapped zero to the target zero.

Protects against a reversed edge that would still satisfy the generic `Edge`
API but swap the comparison direction. -/
noncomputable example :
    (stageWeakDiagonal D).Edge
      (levelZeroEdgeMappedVertex C D F) (stageWeakDiagonalZeroVertex D) :=
  stageWeakDiagonalLevelZeroEdge C D F

/-- Edge formula is `mk₁` of the identity on the edge weak stage.

Protects against an edge built from the wrong morphism while keeping the right
endpoints definitionally. -/
example :
    (stageWeakDiagonalLevelZeroEdge C D F).edge =
      ComposableArrows.mk₁ (𝟙 (levelZeroEdgeWeak C D F)) :=
  stageWeakDiagonalLevelZeroEdge_edge C D F

/-- Source of the edge is the mapped-zero vertex.

Protects against a wrong-endpoint edge that targets the right vertex but starts
elsewhere. -/
example :
    (stageWeakDiagonal D).δ 1 (stageWeakDiagonalLevelZeroEdge C D F).edge =
      levelZeroEdgeMappedVertex C D F :=
  stageWeakDiagonalLevelZeroEdge_src C D F

/-- Target of the edge is the target-zero vertex.

Protects against a wrong-endpoint edge that starts at the mapped zero but lands
elsewhere. -/
example :
    (stageWeakDiagonal D).δ 0 (stageWeakDiagonalLevelZeroEdge C D F).edge =
      stageWeakDiagonalZeroVertex D :=
  stageWeakDiagonalLevelZeroEdge_tgt C D F

/-- Diagonal `(0, 0)` value is the mapped zero.

Protects against swapping the two diagonal faces while keeping the edge
endpoints. -/
example :
    (levelZeroEdgeDiagram C D F).obj (diag (0 : Fin 2)) = F.obj (0 : C) :=
  levelZeroEdgeDiagram_diag_zero C D F

/-- Diagonal `(1, 1)` value is the chosen zero.

Protects against replacing the target face with a second mapped copy. -/
example :
    (levelZeroEdgeDiagram C D F).obj (diag (1 : Fin 2)) = (0 : D) :=
  levelZeroEdgeDiagram_diag_one C D F

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroEdgeTests
