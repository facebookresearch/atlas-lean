/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.EdgewiseResolutionWeakEquivalence

import
  MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence

/-!
# Outer edgewise subdivision and simplicial diagonals

Precomposing the outer simplicial direction of a bisimplicial set with the
edgewise ordinal functor gives its outer edgewise subdivision.  The natural
right-block inclusion induces a comparison to the original bisimplicial set.
After fixing an inner degree this comparison is literally
`SSet.esdComparison` on the corresponding row, so the inner-row diagonal
theorem proves that its simplicial diagonal is a realization weak
equivalence.

This file makes no arbitrary simplicial-topological-space, model-category,
Quillen, Stage, pointed, loop-space, spectrum, or Q/S claim and installs no
global instance.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Opposite

open scoped Simplicial

universe u

namespace SSet

/-- Precompose the outer simplicial direction of a bisimplicial set with the
edgewise ordinal functor. -/
def outerEdgewise :
    SimplicialObject SSet.{u} ⥤ SimplicialObject SSet.{u} :=
  (Functor.whiskeringLeft _ _ _).obj SimplexCategory.edgewiseQ.op

@[simp]
theorem outerEdgewise_obj_obj (B : SimplicialObject SSet.{u})
    (a : SimplexCategoryᵒᵖ) :
    (outerEdgewise.obj B).obj a =
      B.obj (SimplexCategory.edgewiseQ.op.obj a) :=
  rfl

@[simp]
theorem outerEdgewise_obj_map (B : SimplicialObject SSet.{u})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (outerEdgewise.obj B).map f =
      B.map (SimplexCategory.edgewiseQ.op.map f) :=
  rfl

@[simp]
theorem outerEdgewise_map_app {B C : SimplicialObject SSet.{u}}
    (η : B ⟶ C) (a : SimplexCategoryᵒᵖ) :
    (outerEdgewise.map η).app a =
      η.app (SimplexCategory.edgewiseQ.op.obj a) :=
  rfl

/-- The outer-edgewise comparison induced by the straight/right ordinal-sum
inclusion. -/
def outerEdgewiseComparison :
    outerEdgewise.{u} ⟶ Functor.id (SimplicialObject SSet.{u}) where
  app B :=
    { app := fun a =>
        B.map (SimplexCategory.edgewiseRightInclusion.app a.unop).op
      naturality := by
        intro a b f
        change B.map (SimplexCategory.edgewiseQ.op.map f) ≫
            B.map (SimplexCategory.edgewiseRightInclusion.app b.unop).op =
          B.map (SimplexCategory.edgewiseRightInclusion.app a.unop).op ≫
            B.map f
        rw [← B.map_comp, ← B.map_comp]
        apply congrArg B.map
        apply Quiver.Hom.unop_inj
        exact
          (SimplexCategory.edgewiseRightInclusion.naturality f.unop).symm }
  naturality B C η := by
    ext a : 1
    simp only [Functor.id_obj]
    exact (η.naturality
      (SimplexCategory.edgewiseRightInclusion.app a.unop).op).symm

/-- Outer component formula for the outer-edgewise comparison. -/
@[simp]
theorem outerEdgewiseComparison_app_app
    (B : SimplicialObject SSet.{u}) (a : SimplexCategoryᵒᵖ) :
    (outerEdgewiseComparison.app B).app a =
      B.map (SimplexCategory.edgewiseRightInclusion.app a.unop).op :=
  rfl

/-- Bisimplex component formula for the outer-edgewise comparison. -/
@[simp]
theorem outerEdgewiseComparison_app_app_app
    (B : SimplicialObject SSet.{u})
    (a b : SimplexCategoryᵒᵖ) :
    ((outerEdgewiseComparison.app B).app a).app b =
      (B.map
        (SimplexCategory.edgewiseRightInclusion.app a.unop).op).app b :=
  rfl

/-- The map on simplicial diagonals induced by the outer-edgewise
comparison. -/
def outerEdgewiseDiagonalComparison
    (B : SimplicialObject SSet.{u}) :
    simplicialDiagonalFunctor.obj (outerEdgewise.obj B) ⟶
      simplicialDiagonalFunctor.obj B :=
  simplicialDiagonalFunctor.map (outerEdgewiseComparison.app B)

/-- Component formula for the outer-edgewise diagonal comparison. -/
@[simp]
theorem outerEdgewiseDiagonalComparison_app
    (B : SimplicialObject SSet.{u}) (a : SimplexCategoryᵒᵖ) :
    (outerEdgewiseDiagonalComparison B).app a =
      (B.map
        (SimplexCategory.edgewiseRightInclusion.app a.unop).op).app a :=
  rfl

/-- After fixing an inner degree, the outer-edgewise comparison is literally
the ordinary edgewise comparison of that row. -/
theorem outerEdgewiseComparison_transpose_app
    (B : SimplicialObject SSet.{u}) (m : ℕ) :
    (simplicialTransposeFunctor.map
      (outerEdgewiseComparison.app B)).app
        (op (SimplexCategory.mk m)) =
      esdComparison.app
        (simplicialRow B (op (SimplexCategory.mk m))) := by
  ext a x
  rfl

/-- The literal diagonal comparison from outer edgewise subdivision is a
realization weak equivalence. -/
theorem outerEdgewiseDiagonalComparison_mem_realizationWeakEquivalences
    (B : SimplicialObject SSet.{u}) :
    realizationWeakEquivalences
      (outerEdgewiseDiagonalComparison B) := by
  apply
    simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
  intro m
  rw [outerEdgewiseComparison_transpose_app]
  exact esdComparison_mem_realizationWeakEquivalences _

end SSet

end
