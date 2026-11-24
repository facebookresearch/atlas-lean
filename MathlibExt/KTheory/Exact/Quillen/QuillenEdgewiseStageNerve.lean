/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridLift
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Outer-edgewise nerves of weak Waldhausen Stages

Precomposing the Stage degree with the edgewise ordinal functor and taking a
levelwise nerve gives a simplicial object in simplicial sets.  Its outer degree
`a` is the nerve of weak Stages of degree `(edgewiseQ.obj a).len`, and its maps
are induced by the existing strict edgewise Stage reindexing functors.

The canonical simplicial diagonal packages this bisimplicial carrier into one
simplicial set.  It is not definitionally the edgewise subdivision of the
already formed weak-Stage diagonal: edgewise reindexing occurs only in the
outer simplicial direction here.

This file constructs only the outer-edgewise carrier and its diagonal.  It
defines no grid-to-Stage projection, outer-edgewise comparison, realization or
weak-equivalence theorem, basepoint or loop map, or Q/S comparison.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenEdgewiseStageNerveWaldhausenCategory :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- Levelwise nerve of weak Stages in outer-edgewise degree. -/
noncomputable def edgewiseStageWeakNerve
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    SimplicialObject SSet.{max u v} where
  obj a := CategoryTheory.nerve
    (StageWeakCategory C (edgewiseQ.obj a.unop).len)
  map f := CategoryTheory.nerveMap
    (edgewiseStageWeakReindex (C := C) f.unop)
  map_id a := by
    simp only [unop_id, edgewiseStageWeakReindex_id]
    rfl
  map_comp f g := by
    simp only [unop_comp, edgewiseStageWeakReindex_comp]
    rfl

/-- Outer-degree computation for the outer-edgewise weak-Stage nerve. -/
@[simp]
theorem edgewiseStageWeakNerve_obj (a : SimplexCategoryᵒᵖ) :
    (edgewiseStageWeakNerve C).obj a =
      CategoryTheory.nerve
        (StageWeakCategory C (edgewiseQ.obj a.unop).len) :=
  rfl

/-- At numeric outer degree `n`, the weak Stage has degree `2 * n + 1`. -/
@[simp]
theorem edgewiseStageWeakNerve_obj_op_mk (n : ℕ) :
    (edgewiseStageWeakNerve C).obj (op ⦋n⦌) =
      CategoryTheory.nerve (StageWeakCategory C (2 * n + 1)) := by
  rw [edgewiseStageWeakNerve_obj]
  change CategoryTheory.nerve
      (StageWeakCategory C (edgewiseQ.obj ⦋n⦌).len) = _
  rw [edgewiseQ_obj_len]

/-- Outer-map computation for the outer-edgewise weak-Stage nerve. -/
@[simp]
theorem edgewiseStageWeakNerve_map {a b : SimplexCategoryᵒᵖ}
    (f : a ⟶ b) :
    (edgewiseStageWeakNerve C).map f =
      CategoryTheory.nerveMap
        (edgewiseStageWeakReindex (C := C) f.unop) :=
  rfl

/-- Every outer face acts by the nerve of edgewise weak-Stage reindexing. -/
@[simp]
theorem edgewiseStageWeakNerve_map_δ {n : ℕ} (i : Fin (n + 2)) :
    (edgewiseStageWeakNerve C).map (SimplexCategory.δ i).op =
      CategoryTheory.nerveMap
        (edgewiseStageWeakReindex (C := C) (SimplexCategory.δ i)) :=
  rfl

/-- Every outer degeneracy acts by the nerve of edgewise weak-Stage
reindexing. -/
@[simp]
theorem edgewiseStageWeakNerve_map_σ {n : ℕ} (i : Fin (n + 1)) :
    (edgewiseStageWeakNerve C).map (SimplexCategory.σ i).op =
      CategoryTheory.nerveMap
        (edgewiseStageWeakReindex (C := C) (SimplexCategory.σ i)) :=
  rfl

/-- A vertex of a levelwise nerve is reindexed by the edgewise Stage
reindexing functor. -/
@[simp]
theorem edgewiseStageWeakNerve_map_app_mk₀
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b)
    (X : StageWeakCategory C (edgewiseQ.obj a.unop).len) :
    ((edgewiseStageWeakNerve C).map f).app (op ⦋0⦌)
        (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀
        ((edgewiseStageWeakReindex (C := C) f.unop).obj X) :=
  CategoryTheory.nerveMap_app_mk₀ _ _

/-- An edge of a levelwise nerve is reindexed by the edgewise Stage
reindexing functor. -/
@[simp]
theorem edgewiseStageWeakNerve_map_app_mk₁
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b)
    {X Y : StageWeakCategory C (edgewiseQ.obj a.unop).len}
    (φ : X ⟶ Y) :
    ((edgewiseStageWeakNerve C).map f).app (op ⦋1⦌)
        (ComposableArrows.mk₁ φ) =
      ComposableArrows.mk₁
        ((edgewiseStageWeakReindex (C := C) f.unop).map φ) :=
  CategoryTheory.nerveMap_app_mk₁ _ _

/-- Simplicial diagonal of the outer-edgewise weak-Stage nerve. -/
noncomputable abbrev edgewiseStageWeakDiagonal
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    SSet.{max u v} :=
  SSet.simplicialDiagonalFunctor.obj (edgewiseStageWeakNerve C)

/-- A diagonal simplex in degree `a` is an `a`-simplex in the nerve of the
outer-edgewise weak-Stage category at `a`. -/
@[simp]
theorem edgewiseStageWeakDiagonal_obj (a : SimplexCategoryᵒᵖ) :
    (edgewiseStageWeakDiagonal C).obj a =
      ((edgewiseStageWeakNerve C).obj a).obj a :=
  rfl

/-- Numeric-degree computation for the outer-edgewise weak-Stage diagonal. -/
@[simp]
theorem edgewiseStageWeakDiagonal_obj_op_mk (n : ℕ) :
    (edgewiseStageWeakDiagonal C).obj (op ⦋n⦌) =
      (CategoryTheory.nerve
        (StageWeakCategory C (2 * n + 1))).obj (op ⦋n⦌) := by
  rw [edgewiseStageWeakDiagonal_obj, edgewiseStageWeakNerve_obj_op_mk]

/-- A diagonal map first applies the inner nerve map and then the outer
edgewise Stage reindexing map. -/
@[simp]
theorem edgewiseStageWeakDiagonal_map {a b : SimplexCategoryᵒᵖ}
    (f : a ⟶ b) :
    (edgewiseStageWeakDiagonal C).map f =
      ↾fun x =>
        (CategoryTheory.nerveMap
          (edgewiseStageWeakReindex (C := C) f.unop)).app b
            ((CategoryTheory.nerve
              (StageWeakCategory C
                (edgewiseQ.obj a.unop).len)).map f x) :=
  SSet.simplicialDiagonalFunctor_obj_map (edgewiseStageWeakNerve C) f

end AlgebraicKTheory

end
