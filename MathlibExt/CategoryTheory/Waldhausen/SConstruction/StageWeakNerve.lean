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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.SimplicialStageWeak
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Levelwise nerve of weak stages

For a Waldhausen category `C`, `stageWeakNerve C` is the levelwise nerve of
`simplicialStageWeak C`, as a simplicial object in `SSet` obtained by
composition with `CategoryTheory.nerveFunctor`. Object `a` is
`nerve (StageWeakCategory C a.unop.len)`; map `f` is
`nerveMap (reindexStageWeak C f.unop)`, with `mk₀`/`mk₁` computation laws
reused from `nerveMap_app_mk₀`/`mk₁`. Identity and composition follow by
composition from `reindexStageWeak_id`/`comp` (via `simplicialStageWeak`) and
`nerveMap_id`/`comp` (via `nerveFunctor`).

This is levelwise nerve only. It provides no single `SSet`, no diagonal or
bisimplicial diagonal, no realization, no weak-equivalence theorem, no
additivity, no K/G-theory, no spectrum, and no Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Levelwise nerve of weak stages: `[n] ↦ nerve (StageWeakCategory C n)`. -/
def stageWeakNerve : SimplicialObject SSet.{max u v} :=
  simplicialStageWeak C ⋙ CategoryTheory.nerveFunctor

/-- Object computation: degree `a` gives `nerve (StageWeakCategory C a.unop.len)`. -/
@[simp]
theorem stageWeakNerve_obj (a : SimplexCategoryᵒᵖ) :
    (stageWeakNerve C).obj a =
      CategoryTheory.nerve (StageWeakCategory C a.unop.len) :=
  rfl

/-- Map computation: `f` acts by `nerveMap` of weak reindexing along `f.unop`. -/
@[simp]
theorem stageWeakNerve_map {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (stageWeakNerve C).map f =
      CategoryTheory.nerveMap (reindexStageWeak C f.unop) :=
  rfl

/-- `0`-simplex computation for levelwise weak-stage nerve maps. -/
@[simp]
theorem stageWeakNerve_map_app_mk₀ {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b)
    (X : StageWeakCategory C a.unop.len) :
    ((stageWeakNerve C).map f).app (op ⦋0⦌) (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀ ((reindexStageWeak C f.unop).obj X) :=
  CategoryTheory.nerveMap_app_mk₀ _ _

/-- `1`-simplex computation for levelwise weak-stage nerve maps. -/
@[simp]
theorem stageWeakNerve_map_app_mk₁ {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b)
    {X Y : StageWeakCategory C a.unop.len} (φ : X ⟶ Y) :
    ((stageWeakNerve C).map f).app (op ⦋1⦌) (ComposableArrows.mk₁ φ) =
      ComposableArrows.mk₁ ((reindexStageWeak C f.unop).map φ) :=
  CategoryTheory.nerveMap_app_mk₁ _ _

end CategoryTheory.Waldhausen.SConstruction
