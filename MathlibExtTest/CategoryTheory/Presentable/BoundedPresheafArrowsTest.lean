/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.BoundedPresheafArrows

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u uC vC
open CategoryTheory CategoryTheory.Limits

namespace BoundedPresheafArrowsTest
variable {C : Type uC} [Category.{vC} C] [Small.{u} C] [LocallySmall.{u} C]

/-- Native restriction gives an actual Type-u family INSIDE the original property. -/
theorem actual_inside_property_representatives (γ : Cardinal.{u})
    (P : ObjectProperty (Arrow (C ⥤ Type u)))
    (hP : ∀ a, P a → ∀ X : C,
      Cardinal.mk (a.left.obj X) ≤ γ ∧ Cardinal.mk (a.right.obj X) ≤ γ) :
    ∃ (ι : Type u) (r : ι → Arrow (C ⥤ Type u)),
      (∀ i, P (r i)) ∧ ∀ a, P a → ∃ i, Nonempty (a ≅ r i) := by
  let _ : ObjectProperty.EssentiallySmall.{u} P :=
    ObjectProperty.essentiallySmall_presheaf_arrows_of_pointwise_bound γ P hP
  obtain ⟨P₀, hsmall, hP₀, hcover⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{u} P
  let _ : ObjectProperty.Small.{u} P₀ := hsmall
  obtain ⟨ι, r, hr⟩ := ObjectProperty.Small.exists_eq_ofObj.{u} P₀
  refine ⟨ι, r, ?_, ?_⟩
  · intro i
    apply hP₀
    rw [hr]
    exact ObjectProperty.ofObj_apply r i
  · intro a ha
    obtain ⟨b, hb, ⟨eb⟩⟩ := hcover a ha
    rw [hr] at hb
    obtain ⟨i, hi⟩ := (ObjectProperty.ofObj_iff r b).1 hb
    exact ⟨i, ⟨eb ≪≫ eqToIso hi.symm⟩⟩

/-- The chosen actual representative retains BOTH squares and whole inverse equations. -/
theorem actual_original_arrow_data (γ : Cardinal.{u})
    (P : ObjectProperty (Arrow (C ⥤ Type u)))
    (hP : ∀ a, P a → ∀ X : C,
      Cardinal.mk (a.left.obj X) ≤ γ ∧ Cardinal.mk (a.right.obj X) ≤ γ)
    (a : Arrow (C ⥤ Type u)) (ha : P a) :
    ∃ (b : Arrow (C ⥤ Type u)), P b ∧ ∃ (e : a ≅ b),
      e.hom.left ≫ b.hom = a.hom ≫ e.hom.right ∧
      e.inv.left ≫ a.hom = b.hom ≫ e.inv.right ∧
      e.hom ≫ e.inv = 𝟙 a ∧ e.inv ≫ e.hom = 𝟙 b := by
  obtain ⟨ι, r, hr, hcover⟩ := actual_inside_property_representatives γ P hP
  obtain ⟨i, ⟨e⟩⟩ := hcover a ha
  exact ⟨r i, hr i, e, e.hom.w, e.inv.w, e.hom_inv_id, e.inv_hom_id⟩

/-- Empty properties need no nonempty representative index or value type. -/
theorem empty_property_representatives :
    ∃ ι : Type u, IsEmpty ι := by
  obtain ⟨ι, r, hr, _⟩ := actual_inside_property_representatives (C := Discrete PUnit.{1})
    (0 : Cardinal.{u}) (fun _ => False) (fun _ h => h.elim)
  exact ⟨ι, ⟨hr⟩⟩

end BoundedPresheafArrowsTest
