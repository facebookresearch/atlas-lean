/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationRestriction

/-!
# Using restricted strong deformation data

The client retains the supplied maps and obtains all four deformation
equations from the returned data, including the full cylinder restriction.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe v u

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C] {P : Precylinder (𝟭 C)}
variable {Z X V Y : C} {i : X ⟶ Y}

/-- The restriction preserves both supplied maps and proves every local field. -/
theorem restrict_keeps_supplied_maps (D : P.StrongDeformationData i)
    (a : Z ⟶ X) (b : Z ⟶ V) (j : V ⟶ Y) [Mono a] [Mono j]
    (w : a ≫ i = b ≫ j)
    (rV : V ⟶ Z) (hr : rV ≫ a = j ≫ D.retraction)
    (hV : P.I.obj V ⟶ V) (hH : P.I.map j ≫ D.homotopy.h = hV ≫ j) :
    (D.restrict a b j w rV hr hV hH).retraction = rV ∧
      (D.restrict a b j w rV hr hV hH).homotopy.h = hV ∧
      b ≫ rV = 𝟙 Z ∧
      (P.app V).i₀ ≫ hV = 𝟙 V ∧
      (P.app V).i₁ ≫ hV = rV ≫ b ∧
      P.I.map b ≫ hV = (P.app Z).π ≫ b := by
  let E := D.restrict a b j w rV hr hV hH
  exact ⟨rfl, rfl, E.retract, E.homotopy.h₀, E.homotopy.h₁, E.stationary⟩

end HomotopicalAlgebra.Precylinder
