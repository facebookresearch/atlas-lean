/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import MathlibExt.AlgebraicTopology.SimplicialObject.Diagonal
public import MathlibExt.AlgebraicTopology.SimplicialObject.DiagonalPreservesLimits

/-!
# Canonical diagonal functor for simplicial objects in simplicial sets

For `X : SimplicialObject SSet.{u}`, `simplicialDiagonalFunctor.obj X` is the
single `SSet` diagonal with degree `a` given by the `a`-simplices of the
level-`a` set. For `α : X ⟶ Y`, `simplicialDiagonalFunctor.map α` is the
induced diagonal map with component `(α.app a).app a`.

Universe and variance: everything lives over one universe `u`; both simplicial
directions use `SimplexCategoryᵒᵖ`, so `Functor.diag` applies squarely. The
`flip` orientation puts the outer index on the level and the inner index on
the nerve simplices.

The weak-stage diagonal consumes this functor directly: `stageWeakDiagonal C`
is `simplicialDiagonalFunctor.obj (stageWeakNerve C)`, and exact-functor maps
are `simplicialDiagonalFunctor.map (stageWeakNerveMap C D F)` with component
`((stageWeakNerveMap C D F).app a).app a`.

Nonclaims: no realization, weak equivalence, additivity, `π₀`, spectra, or Q/S
comparison.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

universe w' w u

namespace SSet

/-- Canonical diagonal functor from simplicial objects in `SSet` to `SSet`. -/
def simplicialDiagonalFunctor : SimplicialObject SSet.{u} ⥤ SSet.{u} :=
  CategoryTheory.SimplicialObject.diagonalFunctor (Type u)

/-- The simplicial-set diagonal preserves every shape of limits present in
the coefficient category of types. -/
noncomputable instance simplicialDiagonalFunctor_preservesLimitsOfShape
    (J : Type w) [Category.{w'} J] [HasLimitsOfShape J (Type u)] :
    PreservesLimitsOfShape J simplicialDiagonalFunctor.{u} := by
  unfold simplicialDiagonalFunctor
  infer_instance

/-- The diagonal of a constant simplicial object is canonically the original
simplicial set. -/
noncomputable def diagonalConstIso (Z : SSet.{u}) :
    simplicialDiagonalFunctor.obj ((SimplicialObject.const SSet.{u}).obj Z) ≅ Z :=
  CategoryTheory.SimplicialObject.diagonalConstIso (Type u) Z

/-- Object computation: degree `a` is the `a`-simplices of the level-`a` set. -/
@[simp]
theorem simplicialDiagonalFunctor_obj (X : SimplicialObject SSet.{u})
    (a : SimplexCategoryᵒᵖ) :
    (simplicialDiagonalFunctor.obj X).obj a = (X.obj a).obj a :=
  CategoryTheory.SimplicialObject.diagonalFunctor_obj (Type u) X a

/-- Component computation for the functorial diagonal map. -/
@[simp]
theorem simplicialDiagonalFunctor_map_app {X Y : SimplicialObject SSet.{u}}
    (α : X ⟶ Y) (a : SimplexCategoryᵒᵖ) :
    (simplicialDiagonalFunctor.map α).app a = (α.app a).app a :=
  CategoryTheory.SimplicialObject.diagonalFunctor_map_app (Type u) α a

/-- Map computation for the diagonal object: inner simplicial-set map
followed by the outer natural-transformation component. -/
@[simp]
theorem simplicialDiagonalFunctor_obj_map (X : SimplicialObject SSet.{u})
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (simplicialDiagonalFunctor.obj X).map f =
      ↾fun x => (X.map f).app b ((X.obj a).map f x) := by
  change (simplicialDiagonalFunctor.obj X).map f =
    (X.obj a).map f ≫ (X.map f).app b
  exact CategoryTheory.SimplicialObject.diagonalFunctor_obj_map
    (Type u) X f

end SSet
