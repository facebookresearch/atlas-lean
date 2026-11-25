/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinality of natural maps from original total presheaf points

Natural transformations inject into their original actions on the native category
of elements. This gives the total-point exponential bound with independent site
and value universes, including empty point types.
-/

public section
set_option autoImplicit false

noncomputable section

universe u v w

open CategoryTheory Cardinal

namespace CategoryTheory

/-- Natural maps are bounded by functions on their original total presheaf points. -/
theorem mk_hom_le_elements_power {D : Type w} [Category.{v} D]
    (A X : Dᵒᵖ ⥤ Type u) :
    Cardinal.mk (A ⟶ X) ≤ Cardinal.mk X.Elements ^ Cardinal.mk A.Elements := by
  have haction : Function.Injective (fun f : A ⟶ X => f.mapElements.obj) := by
    intro f g h
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro a
    have hpoint : X.elementsMk d (f.app d a) = X.elementsMk d (g.app d a) :=
      congrFun h (A.elementsMk d a)
    have hval : ∀ {e₁ e₂ : X.Elements}, e₁ = e₂ → HEq e₁.val e₂.val := by
      intro e₁ e₂ he
      cases he
      rfl
    exact eq_of_heq (hval hpoint)
  exact (Cardinal.mk_le_of_injective haction).trans_eq
    (by rw [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_id])

end CategoryTheory
