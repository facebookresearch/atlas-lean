/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.ZerothRow

/-! # Public consumers of the raw zeroth-row adjunction -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Rezk.Test

/-- Zeroth-row maps use the actual inner-zero component. -/
example {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y)
    (m : SimplexCategoryᵒᵖ) (x : (X.obj m).obj (op ⦋0⦌)) :
    (zerothRow.map f).app m x = (f.app m).app (op ⦋0⦌) x := rfl

/-- The counit has its literal source-prescribed bidegree value. -/
example (X : SimplicialObject SSet.{u}) (m n : SimplexCategoryᵒᵖ)
    (x : (X.obj m).obj (op ⦋0⦌)) :
    ((zerothRowAdjunction.counit.app X).app m).app n x =
      (X.obj m).map (SimplexCategory.const n.unop ⦋0⦌ 0).op x := by
  rw [zerothRowAdjunction_counit_app]

/-- The same public adjunction supplies both strict triangle equations. -/
example (A : SSet.{u}) (X : SimplicialObject SSet.{u}) :
    simplicialSpaceDiscrete.map (zerothRowAdjunction.unit.app A) ≫
        zerothRowAdjunction.counit.app (simplicialSpaceDiscrete.obj A) =
      𝟙 (simplicialSpaceDiscrete.obj A) ∧
    zerothRowAdjunction.unit.app (zerothRow.obj X) ≫
        zerothRow.map (zerothRowAdjunction.counit.app X) =
      𝟙 (zerothRow.obj X) :=
  ⟨zerothRowAdjunction_left_triangle A, zerothRowAdjunction_right_triangle X⟩

/-- The raw unit is invertible for arbitrary simplicial sets. -/
example (A : SSet.{u}) :
    zerothRowAdjunction.unit.app A ≫ inv (zerothRowAdjunction.unit.app A) =
      𝟙 A := by simp

end SSet.Rezk.Test
