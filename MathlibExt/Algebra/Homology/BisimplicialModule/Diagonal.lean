/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Source-only light data owner. Native validation is UNEXECUTED.
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Products.Basic

/-!
# The original bisimplicial diagonal as a light data functor

This owner contains the unchanged original BisimplicialModule.diagonalFunctor.
The normalization/filtered-total proof owner imports this module. The actual
polynomial tower can use its same original data without importing filtered
totals. No second diagonal, resolution model or operator is introduced.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace BisimplicialModule

variable (C : Type u) [Category.{v} C]

/-- The existing native diagonal and uncurrying functors retain both actual operators. -/
def diagonalFunctor : SimplicialObject (SimplicialObject C) ⥤ SimplicialObject C :=
  Functor.uncurry ⋙
    (Functor.whiskeringLeft SimplexCategoryᵒᵖ
      (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) C).obj (Functor.diag SimplexCategoryᵒᵖ)

end BisimplicialModule

end
