/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- The diagonal uses the same simplex operator in both variables.
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Products.Basic

/-!
# The diagonal of a bisimplicial object

For any category C and a bisimplicial object X with values in C, the diagonal has degree-n
object X_{n,n}. A simplex operator acts simultaneously in both variables. Uncurrying X and
precomposing with the diagonal of the simplex category defines this functor, with the object
and morphism universes of C as stated.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace BisimplicialModule

variable (C : Type u) [Category.{v} C]

/-- The diagonal functor on bisimplicial objects.

Send X to the simplicial object n ↦ X_{n,n}, with each simplex operator applied in both
variables, by uncurrying and diagonal precomposition. -/
def diagonalFunctor : SimplicialObject (SimplicialObject C) ⥤ SimplicialObject C :=
  Functor.uncurry ⋙
    (Functor.whiskeringLeft SimplexCategoryᵒᵖ
      (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) C).obj (Functor.diag SimplexCategoryᵒᵖ)

end BisimplicialModule

end
