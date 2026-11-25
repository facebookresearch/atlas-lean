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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroCoherence

/-!
# Diagonal level-zero coherence consumer tests

Focused public-API checks for the diagonal level-zero coherence packet:
mapped-edge type/orientation from the composite mapped-zero vertex to the
once-mapped zero vertex, the edge formula, endpoint laws via
`stageWeakDiagonalMapLevelZeroEdge_src`/`stageWeakDiagonalMapLevelZeroEdge_tgt`,
the mapped-vertex identity, and the identity degeneracy.
Edge-only in the weak-stage diagonal.

Nonclaims: no general F,G diagonal triangle, no realization, paths, pointed
maps, loop spaces, additivity, π₀/K₀, G-theory, spectra, or Q/S comparison.
-/

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.Waldhausen.SConstruction

open scoped Simplicial

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroCoherenceTests

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

/-- Mapped edge runs from the composite mapped zero to the once-mapped zero.

Protects against a reversed edge that would still satisfy the generic `Edge`
API but swap the transport direction. -/
noncomputable example :
    (stageWeakDiagonal E).Edge
      (levelZeroEdgeMappedVertex C E (F ⋙ G))
      (levelZeroEdgeMappedVertex D E G) :=
  stageWeakDiagonalMapLevelZeroEdge C D F E G

/-- Edge formula is the mapped `mk₁` identity.

Protects against an edge built from the wrong morphism while keeping the right
endpoints definitionally. -/
example :
    (stageWeakDiagonalMapLevelZeroEdge C D F E G).edge =
      ComposableArrows.mk₁ ((mapStageWeak D E G 1).map
        (𝟙 (levelZeroEdgeWeak C D F))) :=
  stageWeakDiagonalMapLevelZeroEdge_edge C D F E G

/-- Source of the mapped edge is the composite mapped-zero vertex.

Protects against a wrong-endpoint edge that targets the right vertex but starts
elsewhere. -/
example :
    (stageWeakDiagonal E).δ 1
      (stageWeakDiagonalMapLevelZeroEdge C D F E G).edge =
    levelZeroEdgeMappedVertex C E (F ⋙ G) :=
  stageWeakDiagonalMapLevelZeroEdge_src C D F E G

/-- Target of the mapped edge is the once-mapped zero vertex.

Protects against a wrong-endpoint edge that starts at the composite vertex but
lands elsewhere. -/
example :
    (stageWeakDiagonal E).δ 0
      (stageWeakDiagonalMapLevelZeroEdge C D F E G).edge =
    levelZeroEdgeMappedVertex D E G :=
  stageWeakDiagonalMapLevelZeroEdge_tgt C D F E G

/-- Mapped-vertex identity over the identity functor.

Protects against an identity regression that introduces a nontrivial vertex. -/
example :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      levelZeroEdgeMappedVertex C C (𝟭 C) = stageWeakDiagonalZeroVertex C) :=
  stageWeakDiagonalLevelZero_mappedVertex_id C

/-- Identity degeneracy: the `𝟭 C` level-zero edge is the transported degenerate edge.

Protects against an identity regression that keeps the right endpoints but loses
degeneracy. -/
noncomputable example :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      SSet.Edge.ofEq
        (SSet.Edge.id (stageWeakDiagonalZeroVertex C))
        (stageWeakDiagonalLevelZero_mappedVertex_id C).symm rfl =
      stageWeakDiagonalLevelZeroEdge C C (𝟭 C)) :=
  stageWeakDiagonalLevelZeroEdge_id C

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroCoherenceTests
