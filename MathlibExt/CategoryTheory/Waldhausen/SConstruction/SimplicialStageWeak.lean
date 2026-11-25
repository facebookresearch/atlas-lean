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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakCategory
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Simplicial stage weak-equivalence object

Covariant simplicial object sending `[n]` to the bundled stage
weak-equivalence category `StageWeakCategory C n` and a simplex map to
contravariant weak-stage reindexing.

Variance is explicit and strict: the opposite-category flip turns the
contravariant `reindexStageWeak` into a covariant simplicial object. Object `a`
is `StageWeakCategory C a.unop.len`; map `f` is weak reindexing along `f.unop`,
reusing the exact `reindexStageWeak` identity/composition laws and opposite
`unop` laws.

Nonclaims: no face/degeneracy wrapper, nerve, realization, Q/S comparison, or
K/G-theory.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Simplicial stage weak-equivalence object: `[n] ↦ StageWeakCategory C n`. -/
def simplicialStageWeak : SimplicialObject Cat.{v, max u v} where
  obj a := Cat.of (StageWeakCategory C a.unop.len)
  map f := (reindexStageWeak C f.unop).toCatHom
  map_id a := by
    simp only [unop_id, reindexStageWeak_id]
    rfl
  map_comp f g := by
    simp only [unop_comp, reindexStageWeak_comp]
    rfl

/-- Object computation: degree `a` gives `StageWeakCategory C a.unop.len`. -/
@[simp]
theorem simplicialStageWeak_obj (a : SimplexCategoryᵒᵖ) :
    (simplicialStageWeak C).obj a = Cat.of (StageWeakCategory C a.unop.len) :=
  rfl

/-- Map computation: `f` acts by weak reindexing along `f.unop`. -/
@[simp]
theorem simplicialStageWeak_map {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (simplicialStageWeak C).map f = (reindexStageWeak C f.unop).toCatHom :=
  rfl

end CategoryTheory.Waldhausen.SConstruction
