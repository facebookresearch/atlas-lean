/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalEdgeNormalization

/-!
# Arbitrary weak-stage diagonal-edge normalization tests

These tests pin recovery of the source and target Stage-one objects, recovery
of the underlying Stage-one map, endpoint transport through `Edge.ofEq`, and
the exact source-first fundamental-groupoid conjugation formula.  They make no
generation, realization, K-zero, or additivity claim.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalEdgeNormalizationTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

variable {x y : (stageWeakDiagonal C).obj (op ⦋0⦌)}
  (e : (stageWeakDiagonal C).Edge x y)

example :
    ComposableArrows.mk₁ (ComposableArrows.hom e.edge) = e.edge :=
  ComposableArrows.mk₁_hom e.edge

example :
    ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ 1)).obj
          (ComposableArrows.left e.edge)) = x :=
  stageWeakDiagonalEdge_source_eq C e

example :
    ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ 0)).obj
          (ComposableArrows.right e.edge)) = y :=
  stageWeakDiagonalEdge_target_eq C e

example :
    (stageWeakDiagonalStageOneMapEdge C
        (ComposableArrows.hom e.edge)).ofEq
          (stageWeakDiagonalEdge_source_eq C e)
          (stageWeakDiagonalEdge_target_eq C e) = e :=
  stageWeakDiagonalEdge_stageOneMapEdge_ofEq C e

example :
    (SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalZeroToVertexEdge C x) ≫
      SSet.FundamentalGroupoid.homMk e) ≫
        inv (SSet.FundamentalGroupoid.homMk
          (stageWeakDiagonalZeroToVertexEdge C y)) =
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalObjectEdge C
          ((stageOneEval C).obj (ComposableArrows.left e.edge).obj)) :=
  stageWeakDiagonalEdge_normalization C e

end StageWeakDiagonalEdgeNormalizationTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

end
