/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Category.Basic
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalZeroEdgeRealization
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroEdge

/-!
# Tests for realized zero-edge normalization

These clients pin the arbitrary-universe path orientation and the mixed-
universe exact-functor level-zero edge application.  They make no path
equality, loop naturality, additivity, weak-equivalence, spectrum, or Q/S
claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial ZeroObject
open CategoryTheory.Waldhausen.SConstruction
open scoped Simplicial

universe v u v₁ u₁ v₂ u₂

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalZeroEdgeRealizationTests

section Generic

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C]
  [WaldhausenCategory C]
variable {x y : (stageWeakDiagonal C).obj (op ⦋0⦌)}
  (e : (stageWeakDiagonal C).Edge x y)
  (hzero : IsZero
    ((stageOneEval C).obj (ComposableArrows.left e.edge).obj))

/-- The edge is followed by the inverse target connector, and the result is
homotopic to the inverse source connector. -/
example :
    ((TopCat.pathEquiv (SSet.realizedEdgePath e)).trans
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalZeroToVertexEdge C y))).symm).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalZeroToVertexEdge C x))).symm :=
  stageWeakDiagonalEdge_comp_zeroConnectorSymm_homotopic_of_isZero
    C e hzero

end Generic

section ExactFunctor

variable (C : Type u₁) [Category.{v₁} C]
  [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D]
  [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

local instance stageWeakDiagonalZeroEdgeRealizationTestsWaldhausenC :
    WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C
local instance stageWeakDiagonalZeroEdgeRealizationTestsWaldhausenD :
    WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

/-- The mixed-universe exact-functor level-zero edge satisfies the generic
zero-valued hypothesis. -/
example :
    ((TopCat.pathEquiv
        (SSet.realizedEdgePath (stageWeakDiagonalLevelZeroEdge C D F))).trans
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalZeroToVertexEdge D
          (stageWeakDiagonalZeroVertex D)))).symm).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalZeroToVertexEdge D
          (levelZeroEdgeMappedVertex C D F)))).symm := by
  apply stageWeakDiagonalEdge_comp_zeroConnectorSymm_homotopic_of_isZero
  rw [stageWeakDiagonalLevelZeroEdge_edge]
  change IsZero (F.obj (0 : C))
  exact F.map_isZero (isZero_zero C)

end ExactFunctor

#print axioms
  stageWeakDiagonalEdge_comp_zeroConnectorSymm_homotopic_of_isZero

end StageWeakDiagonalZeroEdgeRealizationTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
