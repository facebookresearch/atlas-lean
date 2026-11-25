/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyCofreeMatchingLifting
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Genuine component cofibrations in the same original Reedy model

The canonical actual cofree evaluation right adjoint preserves original
trivial fibrations in the full Reedy right class, by its genuine image
matching lift. The same original evaluation adjunction and established
Reedy lifting then prove the actual component cofibration, with
independent category object and Hom universes.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Opposite Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- Hom-sets of `SimplexCategoryᵒᵖ` are finite, so evaluation at a simplex has the right adjoint
given by finite products. -/
local instance : ∀ a b : SimplexCategoryᵒᵖ, HasProductsOfShape (a ⟶ b) C :=
  fun a b => by
    let _ : Finite (a ⟶ b) :=
      Finite.of_equiv (b.unop ⟶ a.unop) (CategoryTheory.opEquiv a b).symm
    infer_instance

/-- Every actual same original Reedy cofibration has a genuine original coefficient cofibration in
every scalar degree. -/
theorem component_cofibration_of_reedyLeft {X Y : SimplicialObject C} (i : X ⟶ Y)
    (hi : reedyLeft (cofibrations C) i) (n : ℕ) : cofibrations C (i.app (op ⦋n⦌)) := by
  rw [← trivialFibrations_llp]
  intro A B p hp
  let q := (CofreeMatching.cofree (C := C) n).map p
  have hq := CofreeMatching.cofreeMap_reedy_trivialFibration p hp n
  have hL : HasLiftingProperty i q :=
    reedyLeft_le_llp_reedyRight (cofibrations C) (trivialFibrations C)
      (by rw [trivialFibrations_llp]) i hi q hq
  exact (evaluationAdjunctionLeft C (op ⦋n⦌)).hasLiftingProperty_iff i p |>.mpr hL

end CategoryTheory.SimplicialObject
