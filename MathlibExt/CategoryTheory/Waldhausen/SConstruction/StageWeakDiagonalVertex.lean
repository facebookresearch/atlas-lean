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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonal
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZero
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Weak-diagonal zero vertex source

Simplicial-only zero point for the weak-stage diagonal: `stageWeakDiagonalZeroVertex C`
is the degree-zero simplex given by `ComposableArrows.mk₀` of the weak-category object
wrapping `stageZero C`, with the canonical `Δ[0] ⟶ stageWeakDiagonal C` inclusion via
`SSet.const`.

Simplicial data only. It provides no realization, paths/basepoint coherence,
connectedness, additivity, K/G-theory, spectrum, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Degree-zero vertex of the weak-stage diagonal from the canonical zero stage. -/
noncomputable def stageWeakDiagonalZeroVertex :
    (stageWeakDiagonal C).obj (op ⦋0⦌) :=
  ComposableArrows.mk₀ (⟨stageZero C⟩ : StageWeakCategory C 0)

/-- Canonical zero-vertex inclusion into the weak-stage diagonal. -/
noncomputable def stageWeakDiagonalZeroInclusion :
    Δ[0] ⟶ stageWeakDiagonal C :=
  SSet.const (stageWeakDiagonalZeroVertex C)

/-- The zero-vertex inclusion sends the degree-zero point to the zero vertex. -/
@[simp]
theorem stageWeakDiagonalZeroInclusion_app_zero
    (x : (Δ[0] : SSet).obj (op ⦋0⦌)) :
    (stageWeakDiagonalZeroInclusion C).app (op ⦋0⦌) x =
      stageWeakDiagonalZeroVertex C := by
  unfold stageWeakDiagonalZeroInclusion
  simp only [SSet.const_app, SimplexCategory.const_eq_id, op_id, Functor.map_id,
    CategoryTheory.id_apply, TypeCat.hom_ofHom, TypeCat.Fun.mk_apply]

end CategoryTheory.Waldhausen.SConstruction
