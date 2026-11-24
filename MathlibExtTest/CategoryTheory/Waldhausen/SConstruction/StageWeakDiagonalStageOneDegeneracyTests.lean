/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalStageOneDegeneracy

/-!
# Generic Stage-one degeneracy-square tests

These tests pin the generic map and identity edges, both collapsed reindex
interfaces, the exact source/target triangle face orders, their groupoid
relations, and specialization to the landed weak-equivalence triangles.
They make no counit, arbitrary-edge, realization, K-zero, or additivity claim.
-/

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalStageOneDegeneracyTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

variable {A B : StageWeakCategory C 1} (φ : A ⟶ B)

example :
    (stageWeakDiagonal C).Edge
      (ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ 1)).obj A))
      (ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ 0)).obj B)) :=
  stageWeakDiagonalStageOneMapEdge C φ

example :
    (stageWeakDiagonalStageOneMapEdge C φ).edge =
      ComposableArrows.mk₁ φ :=
  stageWeakDiagonalStageOneMapEdge_edge C φ

example (A : StageWeakCategory C 1) :
    (stageWeakDiagonalStageOneIdentityEdge C A).edge =
      ComposableArrows.mk₁ (𝟙 A) :=
  stageWeakDiagonalStageOneIdentityEdge_edge C A

example (A : StageWeakCategory C 1) :
    (reindexStageWeak C (SimplexCategory.δ (0 : Fin 3))).obj
        ((reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).obj A) =
      (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
        ((reindexStageWeak C (SimplexCategory.δ (0 : Fin 2))).obj A) :=
  reindexStageWeak_sigmaOne_d0_obj C A

example
    (hA := reindexStageWeak_sigmaOne_d0_obj C A)
    (hB := reindexStageWeak_sigmaOne_d0_obj C B) :
    (reindexStageWeak C (SimplexCategory.δ (0 : Fin 3))).map
        ((reindexStageWeak C (SimplexCategory.σ (1 : Fin 2))).map φ) =
      eqToHom hA ≫
        (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).map
          ((reindexStageWeak C (SimplexCategory.δ (0 : Fin 2))).map φ) ≫
        eqToHom hB.symm :=
  reindexStageWeak_sigmaOne_d0_map C φ hA hB

example (A : StageWeakCategory C 1) :
    (reindexStageWeak C (SimplexCategory.δ (2 : Fin 3))).obj
        ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).obj A) =
      (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
        ((reindexStageWeak C (SimplexCategory.δ (1 : Fin 2))).obj A) :=
  reindexStageWeak_sigmaZero_d2_obj C A

example
    (hA := reindexStageWeak_sigmaZero_d2_obj C A)
    (hB := reindexStageWeak_sigmaZero_d2_obj C B) :
    (reindexStageWeak C (SimplexCategory.δ (2 : Fin 3))).map
        ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 2))).map φ) =
      eqToHom hA ≫
        (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).map
          ((reindexStageWeak C (SimplexCategory.δ (1 : Fin 2))).map φ) ≫
        eqToHom hB.symm :=
  reindexStageWeak_sigmaZero_d2_map C φ hA hB

example :
    (stageWeakDiagonal C).δ 2
        (stageWeakDiagonalStageOneSourceTriangleSimplex C φ) =
      (stageWeakDiagonalStageOneIdentityEdge C A).edge :=
  stageWeakDiagonalStageOneSourceTriangle_d2 C φ

example :
    (stageWeakDiagonal C).δ 0
        (stageWeakDiagonalStageOneSourceTriangleSimplex C φ) =
      (stageWeakDiagonalStageZeroMapEdge C
        ((reindexStageWeak C (SimplexCategory.δ 0)).map φ)).edge :=
  stageWeakDiagonalStageOneSourceTriangle_d0 C φ

example :
    (stageWeakDiagonal C).δ 1
        (stageWeakDiagonalStageOneSourceTriangleSimplex C φ) =
      (stageWeakDiagonalStageOneMapEdge C φ).edge :=
  stageWeakDiagonalStageOneSourceTriangle_d1 C φ

example :
    SSet.Edge.CompStruct
      (stageWeakDiagonalStageOneIdentityEdge C A)
      (stageWeakDiagonalStageZeroMapEdge C
        ((reindexStageWeak C (SimplexCategory.δ 0)).map φ))
      (stageWeakDiagonalStageOneMapEdge C φ) :=
  stageWeakDiagonalStageOneSourceCompStruct C φ

example :
    (stageWeakDiagonal C).δ 2
        (stageWeakDiagonalStageOneTargetTriangleSimplex C φ) =
      (stageWeakDiagonalStageZeroMapEdge C
        ((reindexStageWeak C (SimplexCategory.δ 1)).map φ)).edge :=
  stageWeakDiagonalStageOneTargetTriangle_d2 C φ

example :
    (stageWeakDiagonal C).δ 0
        (stageWeakDiagonalStageOneTargetTriangleSimplex C φ) =
      (stageWeakDiagonalStageOneIdentityEdge C B).edge :=
  stageWeakDiagonalStageOneTargetTriangle_d0 C φ

example :
    (stageWeakDiagonal C).δ 1
        (stageWeakDiagonalStageOneTargetTriangleSimplex C φ) =
      (stageWeakDiagonalStageOneMapEdge C φ).edge :=
  stageWeakDiagonalStageOneTargetTriangle_d1 C φ

example :
    SSet.Edge.CompStruct
      (stageWeakDiagonalStageZeroMapEdge C
        ((reindexStageWeak C (SimplexCategory.δ 1)).map φ))
      (stageWeakDiagonalStageOneIdentityEdge C B)
      (stageWeakDiagonalStageOneMapEdge C φ) :=
  stageWeakDiagonalStageOneTargetCompStruct C φ

example :
    SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageOneIdentityEdge C A) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageZeroMapEdge C
          ((reindexStageWeak C (SimplexCategory.δ 0)).map φ)) =
    SSet.FundamentalGroupoid.homMk
      (stageWeakDiagonalStageOneMapEdge C φ) :=
  stageWeakDiagonalStageOneSource_homMk_comp C φ

example :
    SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageZeroMapEdge C
          ((reindexStageWeak C (SimplexCategory.δ 1)).map φ)) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageOneIdentityEdge C B) =
    SSet.FundamentalGroupoid.homMk
      (stageWeakDiagonalStageOneMapEdge C φ) :=
  stageWeakDiagonalStageOneTarget_homMk_comp C φ

section WeakEquivalenceSpecialization

variable {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f)

example :
    stageWeakDiagonalStageOneSourceTriangleSimplex C
        (stageOneWeakMap C f hf) =
      stageWeakDiagonalWeakEquivalenceSourceTriangleSimplex C f hf :=
  stageWeakDiagonalStageOneSourceTriangle_stageOneWeakMap C f hf

example :
    stageWeakDiagonalStageOneTargetTriangleSimplex C
        (stageOneWeakMap C f hf) =
      stageWeakDiagonalWeakEquivalenceTargetTriangleSimplex C f hf :=
  stageWeakDiagonalStageOneTargetTriangle_stageOneWeakMap C f hf

end WeakEquivalenceSpecialization

end StageWeakDiagonalStageOneDegeneracyTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

end
