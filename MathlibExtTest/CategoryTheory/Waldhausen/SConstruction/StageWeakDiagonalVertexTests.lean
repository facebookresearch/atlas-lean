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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalVertex

/-!
# Weak-diagonal zero-vertex consumer test

Focused public-API check for `stageWeakDiagonalZeroVertex` and
`stageWeakDiagonalZeroInclusion`: the `Δ[0]` inclusion at degree one evaluates
to `mk₁` of the identity on the reindexed weak-category `stageZero`.
Simplicial data only.
No realization, paths, additivity, K/G-theory, or Q/S comparison content.
-/

open CategoryTheory Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalVertexTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Degree-one inclusion pins the reindexed weak-category zero stage.

Protects against wiring the diagonal zero vertex to the wrong stage degree, to
the plain `Stage` zero instead of the weak-equivalence wide subcategory, or wiring
the inclusion to a different vertex while still satisfying the generic `SSet.const`
application law. -/
example (x : (Δ[0] : SSet).obj (Opposite.op ⦋1⦌)) :
    (stageWeakDiagonalZeroInclusion C).app (Opposite.op ⦋1⦌) x =
      ComposableArrows.mk₁
        (𝟙 ((reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).obj
          (⟨stageZero C⟩ : StageWeakCategory C 0))) := by
  have h_inc : stageWeakDiagonalZeroInclusion C =
      SSet.const (stageWeakDiagonalZeroVertex C) :=
    rfl
  have h_vertex : stageWeakDiagonalZeroVertex C =
      ComposableArrows.mk₀ (⟨stageZero C⟩ : StageWeakCategory C 0) :=
    rfl
  have h_const (y : (Δ[0] : SSet).obj (Opposite.op ⦋1⦌)) :
      (SSet.const
          (ComposableArrows.mk₀ (⟨stageZero C⟩ : StageWeakCategory C 0))).app
          (Opposite.op ⦋1⦌) y =
        (stageWeakDiagonal C).map
          ((Opposite.op ⦋1⦌).unop.const _ 0).op
          (ComposableArrows.mk₀ (⟨stageZero C⟩ : StageWeakCategory C 0)) :=
    rfl
  rw [h_inc, h_vertex, h_const x]
  have hσ : (Opposite.op ⦋1⦌).unop.const _ 0 = SimplexCategory.σ (0 : Fin 1) :=
    Subsingleton.elim _ _
  rw [hσ]
  have h_inner :
      (CategoryTheory.nerve (StageWeakCategory C 0)).map
          (SimplexCategory.σ (0 : Fin 1)).op
          (ComposableArrows.mk₀ (⟨stageZero C⟩ : StageWeakCategory C 0)) =
        ComposableArrows.mk₁
          (𝟙 (⟨stageZero C⟩ : StageWeakCategory C 0)) := by
    have h := CategoryTheory.nerve.σ₀_mk₀_eq
      (C := StageWeakCategory C 0) (⟨stageZero C⟩ : StageWeakCategory C 0)
    rwa [CategoryTheory.SimplicialObject.σ_def] at h
  have h_applied :
      (stageWeakDiagonal C).map (SimplexCategory.σ (0 : Fin 1)).op
          (ComposableArrows.mk₀ (⟨stageZero C⟩ : StageWeakCategory C 0)) =
        (CategoryTheory.nerveMap
            (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1)))).app
          (Opposite.op ⦋1⦌)
          ((CategoryTheory.nerve (StageWeakCategory C 0)).map
            (SimplexCategory.σ (0 : Fin 1)).op
            (ComposableArrows.mk₀ (⟨stageZero C⟩ : StageWeakCategory C 0))) := rfl
  rw [h_applied, h_inner, CategoryTheory.nerveMap_app_mk₁]
  exact congrArg ComposableArrows.mk₁ (CategoryTheory.Functor.map_id _ _)

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalVertexTests
