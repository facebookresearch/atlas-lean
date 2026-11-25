/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Native monicity from disjoint original coproduct images in Type

For an actual colimiting binary cofan, the two original images cover its
point. Injectivity on each image and disjointness of their target images
therefore prove monicity of the original outgoing map. The cofan point
and both original inclusions remain unchanged.
-/

universe u
open CategoryTheory Limits

namespace CategoryTheory.Limits.Types

/-- Injective disjoint images of a native binary coproduct make the whole original map monic. -/
theorem binaryCofan_mono_of_disjoint {X Y Z : Type u} {c : BinaryCofan X Y}
    (hc : IsColimit c) (g : c.pt ⟶ Z)
    (h₀ : Function.Injective (c.inl ≫ g)) (h₁ : Function.Injective (c.inr ≫ g))
    (hd : Disjoint (Set.range (c.inl ≫ g)) (Set.range (c.inr ≫ g))) : Mono g := by
  apply (CategoryTheory.mono_iff_injective _).mpr
  have hcover := ((binaryCofan_isColimit_iff c).mp ⟨hc⟩).2.2.sup_eq_top
  have cover (z : c.pt) : z ∈ Set.range c.inl ∨ z ∈ Set.range c.inr := by
    change z ∈ Set.range c.inl ⊔ Set.range c.inr
    rw [hcover]
    trivial
  intro a b h
  rcases cover a with ⟨a', rfl⟩ | ⟨a', rfl⟩
  · rcases cover b with ⟨b', rfl⟩ | ⟨b', rfl⟩
    · exact congrArg c.inl (h₀ h)
    · exact False.elim (Set.disjoint_left.mp hd ⟨a', rfl⟩ ⟨b', h.symm⟩)
  · rcases cover b with ⟨b', rfl⟩ | ⟨b', rfl⟩
    · exact False.elim (Set.disjoint_left.mp hd ⟨b', h.symm⟩ ⟨a', rfl⟩)
    · exact congrArg c.inr (h₁ h)

end CategoryTheory.Limits.Types
