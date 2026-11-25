/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Transporting comonoid objects along isomorphisms

This file supplies the comonoid dual of Mathlib's `MonObj.ofIso`.  A
comonoid structure on `M` transports across an isomorphism `M ≅ X`; the
isomorphism becomes a comonoid isomorphism by construction.

## Main declaration

* `CategoryTheory.ComonObj.ofIso`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory
open scoped ComonObj

universe v u

namespace CategoryTheory.ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Transfer a `ComonObj` structure along an isomorphism. -/
@[simps! -isSimp, instance_reducible]
noncomputable def ofIso {M X : C} [ComonObj M] (e : M ≅ X) : ComonObj X where
  counit := e.inv ≫ ε[M]
  comul := e.inv ≫ Δ[M] ≫ (e.hom ⊗ₘ e.hom)
  counit_comul := by
    rw [← cancel_mono (λ_ X).hom]
    simp only [comp_whiskerRight, Category.assoc, Iso.inv_hom_id]
    slice_lhs 3 4 => rw [MonoidalCategory.tensorHom_comp_whiskerRight]
    simp only [Iso.hom_inv_id, id_tensorHom]
    rw [MonoidalCategory.whisker_exchange]
    simp
  comul_counit := by
    rw [← cancel_mono (ρ_ X).hom]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, Iso.inv_hom_id]
    slice_lhs 3 4 => rw [MonoidalCategory.tensorHom_comp_whiskerLeft]
    simp only [Iso.hom_inv_id, tensorHom_id]
    rw [← MonoidalCategory.whisker_exchange]
    simp
  comul_assoc := by
    simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight,
      Category.assoc]
    slice_lhs 3 4 => rw [MonoidalCategory.tensorHom_comp_whiskerLeft]
    simp only [Iso.hom_inv_id, tensorHom_id]
    slice_lhs 3 4 => rw [← MonoidalCategory.whisker_exchange]
    slice_lhs 4 5 => rw [← MonoidalCategory.tensorHom_def]
    slice_rhs 3 4 => rw [MonoidalCategory.tensorHom_comp_whiskerRight]
    simp only [Iso.hom_inv_id, id_tensorHom]
    slice_rhs 3 4 => rw [MonoidalCategory.whisker_exchange]
    slice_rhs 4 5 => rw [← MonoidalCategory.tensorHom_def']
    rw [MonoidalCategory.associator_naturality]
    slice_lhs 2 3 => rw [ComonObj.comul_assoc]
    simp only [Category.assoc]

end CategoryTheory.ComonObj
