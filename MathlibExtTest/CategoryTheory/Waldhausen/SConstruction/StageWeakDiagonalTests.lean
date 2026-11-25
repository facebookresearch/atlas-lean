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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonal

/-!
# Single-set weak-stage diagonal consumer tests

Focused public-API check for `stageWeakDiagonal`: a degenerate
`mk₀` vertex maps to the identity edge on the reindexed object. No
realization, weak-equivalence, additivity, or Q/S comparison content.
-/

open CategoryTheory Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Degenerate `mk₀` vertices map to the identity edge on the reindexed object.

Protects against an object/morphism mismatch where the diagonal action confuses
0-simplices with 1-simplices or reindexes objects differently from the stated
`mk₀` computation law. -/
example (X : StageWeakCategory C 0) :
    (stageWeakDiagonal C).map (SimplexCategory.σ (0 : Fin 1)).op
      (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₁
        (𝟙 ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj X)) := by
  have h_inner :
      (CategoryTheory.nerve (StageWeakCategory C 0)).map
          (SimplexCategory.σ (0 : Fin 1)).op (ComposableArrows.mk₀ X) =
        ComposableArrows.mk₁ (𝟙 X) := by
    have h := CategoryTheory.nerve.σ₀_mk₀_eq (C := StageWeakCategory C 0) X
    rwa [CategoryTheory.SimplicialObject.σ_def] at h
  have h_applied :
      (stageWeakDiagonal C).map (SimplexCategory.σ (0 : Fin 1)).op
          (ComposableArrows.mk₀ X) =
        (CategoryTheory.nerveMap
            (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)))).app
          (Opposite.op ⦋1⦌)
          ((CategoryTheory.nerve (StageWeakCategory C 0)).map
            (SimplexCategory.σ (0 : Fin 1)).op (ComposableArrows.mk₀ X)) := rfl
  rw [h_applied, h_inner, CategoryTheory.nerveMap_app_mk₁]
  exact congrArg ComposableArrows.mk₁ (CategoryTheory.Functor.map_id _ _)

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalTests
