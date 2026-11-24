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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Reindex
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Simplicial Waldhausen-stage object

Covariant simplicial object sending `[n]` to the bundled finite stage
`Stage C n` and a simplex map to contravariant stage reindexing.

Variance is explicit and strict: the opposite-category flip turns the
contravariant `reindexStage` into a covariant simplicial object. Object `a`
is `Stage C a.unop.len`; map `f` is reindexing along `f.unop`, reusing the
exact `reindexStage` identity/composition laws and opposite `unop` laws.

Nonclaims: no face/degeneracy wrapper, weak-equivalence category or nerve,
realization, Q/S comparison, or K/G-theory.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Simplicial Waldhausen-stage object: `[n] ↦ Stage C n` with reindexing maps. -/
def simplicialStage : SimplicialObject Cat.{v, max u v} where
  obj a := Cat.of (Stage C a.unop.len)
  map f := (reindexStage f.unop).toCatHom
  map_id a := by
    simp only [unop_id, reindexStage_id]
    rfl
  map_comp f g := by
    simp only [unop_comp, reindexStage_comp]
    rfl

/-- Object computation: degree `a` gives `Stage C a.unop.len`. -/
@[simp]
theorem simplicialStage_obj (a : SimplexCategoryᵒᵖ) :
    (simplicialStage C).obj a = Cat.of (Stage C a.unop.len) :=
  rfl

/-- Map computation: `f` acts by reindexing along `f.unop`. -/
@[simp]
theorem simplicialStage_map {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (simplicialStage C).map f = (reindexStage f.unop).toCatHom :=
  rfl

end CategoryTheory.Waldhausen.SConstruction
