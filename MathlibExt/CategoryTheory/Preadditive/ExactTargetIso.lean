/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Original composition exactness under an actual target isomorphism

The SAME two original arrows are tested against both targets. The full
target isomorphism and its original inverse transport image and zero
kernel witnesses, retaining every composition map.
-/

@[expose] public section

universe u v

namespace CategoryTheory.Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The SAME image/zero-kernel equality transports through the actual target Iso. -/
theorem exact_target_iso {U V W E E' : C} (p : U ⟶ V) (q : V ⟶ W) (e : E ≅ E')
    (he : ∀ f : V ⟶ E', (∃ h : W ⟶ E', q ≫ h = f) ↔ p ≫ f = 0) (f : V ⟶ E) :
    (∃ h : W ⟶ E, q ≫ h = f) ↔ p ≫ f = 0 := by
  constructor
  · rintro ⟨h, hh⟩
    have hk : p ≫ (f ≫ e.hom) = 0 := (he (f ≫ e.hom)).mp
      ⟨h ≫ e.hom, by rw [← Category.assoc, hh]⟩
    apply (cancel_mono e.hom).mp
    rw [Limits.zero_comp, Category.assoc]
    exact hk
  · intro hk
    obtain ⟨h, hh⟩ := (he (f ≫ e.hom)).mpr (by rw [← Category.assoc, hk, Limits.zero_comp])
    refine ⟨h ≫ e.inv, ?_⟩
    rw [← Category.assoc, hh, Category.assoc, e.hom_inv_id, Category.comp_id]

end CategoryTheory.Preadditive
