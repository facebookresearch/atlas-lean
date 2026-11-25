/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalZeroContraction

/-!
# Stage-zero diagonal contraction tests

These tests pin thinness, the natural contraction, connector and map-edge
formulas, the connector naturality triangle, and its fundamental-groupoid
relation.  They make no Stage-one, arbitrary-edge, realization, K-zero,
additivity, or Q/S claim.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalZeroContractionTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

example {S T : StageWeakCategory C 0} (f g : S ⟶ T) : f = g :=
  stageWeakZero_hom_ext C f g

example : Quiver.IsThin (StageWeakCategory C 0) := inferInstance

example (T : StageWeakCategory C 0) :
    (⟨stageZero C⟩ : StageWeakCategory C 0) ≅ T :=
  stageWeakZeroIso C T

example :
    (Functor.const (StageWeakCategory C 0)).obj
        (⟨stageZero C⟩ : StageWeakCategory C 0) ≅
      𝟭 (StageWeakCategory C 0) :=
  stageWeakZeroContraction C

example (T : StageWeakCategory C 0) :
    (stageWeakZeroContraction C).hom.app T =
      (stageWeakZeroIso C T).hom :=
  stageWeakZeroContraction_hom_app C T

example {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakZeroIso C S).hom ≫ f = (stageWeakZeroIso C T).hom :=
  stageWeakZeroToObj_naturality C f

example (T : StageWeakCategory C 0) (i : Fin 2) :
    ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)) ⋙
      reindexStageWeak C (SimplexCategory.δ i)).obj T) = T :=
  reindexStageWeak_sigmaZero_delta_obj C T i

example (T : StageWeakCategory C 0) :
    (stageWeakDiagonal C).Edge (stageWeakDiagonalZeroVertex C)
      (ComposableArrows.mk₀ T) :=
  stageWeakDiagonalZeroToObjEdge C T

example (T : StageWeakCategory C 0) :
    (stageWeakDiagonalZeroToObjEdge C T).edge =
      ComposableArrows.mk₁
        ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).map
          (stageWeakZeroIso C T).hom) :=
  stageWeakDiagonalZeroToObjEdge_edge C T

example (T : StageWeakCategory C 0) :
    (stageWeakDiagonal C).δ 1
        (stageWeakDiagonalZeroToObjEdge C T).edge =
      stageWeakDiagonalZeroVertex C :=
  stageWeakDiagonalZeroToObjEdge_src C T

example (T : StageWeakCategory C 0) :
    (stageWeakDiagonal C).δ 0
        (stageWeakDiagonalZeroToObjEdge C T).edge =
      ComposableArrows.mk₀ T :=
  stageWeakDiagonalZeroToObjEdge_tgt C T

example (x : (stageWeakDiagonal C).obj (op ⦋0⦌)) :
    (stageWeakDiagonal C).Edge (stageWeakDiagonalZeroVertex C) x :=
  stageWeakDiagonalZeroToVertexEdge C x

example (x : (stageWeakDiagonal C).obj (op ⦋0⦌)) :
    (stageWeakDiagonalZeroToVertexEdge C x).edge =
      (stageWeakDiagonalZeroToObjEdge C
        (CategoryTheory.nerveEquiv x)).edge :=
  stageWeakDiagonalZeroToVertexEdge_edge C x

example {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).Edge (ComposableArrows.mk₀ S)
      (ComposableArrows.mk₀ T) :=
  stageWeakDiagonalStageZeroMapEdge C f

example {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonalStageZeroMapEdge C f).edge =
      ComposableArrows.mk₁
        ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).map f) :=
  stageWeakDiagonalStageZeroMapEdge_edge C f

example {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).δ 1
        (stageWeakDiagonalStageZeroMapEdge C f).edge =
      ComposableArrows.mk₀ S :=
  stageWeakDiagonalStageZeroMapEdge_src C f

example {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).δ 0
        (stageWeakDiagonalStageZeroMapEdge C f).edge =
      ComposableArrows.mk₀ T :=
  stageWeakDiagonalStageZeroMapEdge_tgt C f

example {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).δ 2
        (stageWeakDiagonalZeroConnectorSimplex C f) =
      (stageWeakDiagonalZeroToObjEdge C S).edge :=
  stageWeakDiagonalZeroConnectorSimplex_d2 C f

example {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).δ 0
        (stageWeakDiagonalZeroConnectorSimplex C f) =
      (stageWeakDiagonalStageZeroMapEdge C f).edge :=
  stageWeakDiagonalZeroConnectorSimplex_d0 C f

example {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    (stageWeakDiagonal C).δ 1
        (stageWeakDiagonalZeroConnectorSimplex C f) =
      (stageWeakDiagonalZeroToObjEdge C T).edge :=
  stageWeakDiagonalZeroConnectorSimplex_d1 C f

example {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    SSet.Edge.CompStruct
      (stageWeakDiagonalZeroToObjEdge C S)
      (stageWeakDiagonalStageZeroMapEdge C f)
      (stageWeakDiagonalZeroToObjEdge C T) :=
  stageWeakDiagonalZeroConnectorCompStruct C f

example {S T : StageWeakCategory C 0} (f : S ⟶ T) :
    SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalZeroToObjEdge C S) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageZeroMapEdge C f) =
    SSet.FundamentalGroupoid.homMk
      (stageWeakDiagonalZeroToObjEdge C T) :=
  stageWeakDiagonalZeroConnector_homMk_comp C f

example :
    stageWeakDiagonalZeroToObjEdge C
        (⟨stageZero C⟩ : StageWeakCategory C 0) =
      SSet.Edge.id (stageWeakDiagonalZeroVertex C) :=
  stageWeakDiagonalZeroToObjEdge_zero C

example :
    SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalZeroToObjEdge C
          (⟨stageZero C⟩ : StageWeakCategory C 0)) =
      𝟙 _ :=
  stageWeakDiagonalZeroToObjEdge_zero_homMk C

end StageWeakDiagonalZeroContractionTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

end
