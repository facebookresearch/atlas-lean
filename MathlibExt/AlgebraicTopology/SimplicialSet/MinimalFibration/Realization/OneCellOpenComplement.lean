/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.PushoutOpenComplement

/-! # One-cell open complement homeomorphism

Purpose: trivialize the complement of the old-cell image in a one-cell
pushout as the preimage homeomorphism needed for the ambient cover.

Hypotheses: a `TopCat` pushout `sq : IsPushout t l r b` and a closed-embedding
hypothesis `IsClosedEmbedding r.hom` on the old leg.

Route: take `U := (Set.range r.hom)ᶜ`; openness from the closed range,
`r ⁻¹' U = ∅` since every `r x` lies in its range, `b ⁻¹' U ⊆ (range l.hom)ᶜ`
from `sq.w`, then `isHomeomorph_restrictPreimage_inr_of_isPushout`.

Nonclaims: no whole-apex GoodPair pushout, no raw-image openness, no global
chart, and no model-category instance.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace TopCat

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/-- Ambient open complement of the old-cell image. -/
theorem isOpen_oneCellOpenComplement (hr_closed : IsClosedEmbedding r.hom) :
    IsOpen ((Set.range r.hom)ᶜ) :=
  hr_closed.isClosed_range.isOpen_compl

/-- The old leg misses its open complement. -/
theorem preimage_oneCellOpenComplement_self :
    r ⁻¹' ((Set.range r.hom)ᶜ) = ∅ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range,
    Set.mem_empty_iff_false]
  constructor
  · intro h
    exact h ⟨x, rfl⟩
  · intro h
    exact h.elim

/-- The new-leg preimage lies off the old-leg domain image. -/
theorem preimage_oneCellOpenComplement_subset (sq : IsPushout t l r b) :
    b ⁻¹' ((Set.range r.hom)ᶜ) ⊆ (Set.range l.hom)ᶜ := by
  intro x hx hmem
  obtain ⟨s, hs⟩ := hmem
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range] at hx
  apply hx
  refine ⟨t s, ?_⟩
  have hcomm : r (t s) = b (l s) := by
    change (t ≫ r) s = (l ≫ b) s
    rw [sq.w]
  have hs_bare : l s = x := hs
  rw [hs_bare] at hcomm
  exact hcomm

/-- The new-leg preimage equals the complement of the old-leg domain image. -/
theorem preimage_oneCellOpenComplement_eq (sq : IsPushout t l r b) :
    b ⁻¹' ((Set.range r.hom)ᶜ) = (Set.range l.hom)ᶜ := by
  apply Set.Subset.antisymm (preimage_oneCellOpenComplement_subset sq)
  intro x hx
  rw [Set.mem_compl_iff] at hx
  rw [Set.mem_preimage, Set.mem_compl_iff]
  intro hmem
  obtain ⟨z, hz⟩ := hmem
  exact CategoryTheory.Limits.Types.pushoutCocone_inl_ne_inr_of_not_mem_range_of_isColimit
    (sq.map (forget TopCat)).isColimit hx hz

/-- Preimage homeomorphism over the one-cell open complement. -/
theorem isHomeomorph_oneCellOpenComplement_restrictPreimage
    (sq : IsPushout t l r b) (hr_closed : IsClosedEmbedding r.hom) :
    IsHomeomorph (((Set.range r.hom)ᶜ).restrictPreimage b) := by
  exact isHomeomorph_restrictPreimage_inr_of_isPushout sq
    (isOpen_oneCellOpenComplement hr_closed)
    preimage_oneCellOpenComplement_self
    (preimage_oneCellOpenComplement_subset sq)

end TopCat
