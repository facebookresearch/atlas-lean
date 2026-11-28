/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.PushoutOpenComplement

/-!
# Complements in topological pushouts

Let `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶ X₄`, and `b : X₃ ⟶ X₄` form a pushout in
`TopCat.{u}`. Write `U = (Set.range r.hom)ᶜ`. Then `r ⁻¹' U = ∅` and `b ⁻¹' U = (Set.range
l.hom)ᶜ`. If `r` is a closed embedding, `U` is open and restriction of `b` gives a
homeomorphism from `b ⁻¹' U`, with its subspace topology, to `U`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace TopCat

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/-- For a morphism `r : X₂ ⟶ X₄` in `TopCat.{u}`, if `r.hom` is a closed embedding, then
`(Set.range r.hom)ᶜ` is open in `X₄`. -/
theorem isOpen_oneCellOpenComplement (hr_closed : IsClosedEmbedding r.hom) :
    IsOpen ((Set.range r.hom)ᶜ) :=
  hr_closed.isClosed_range.isOpen_compl

/-- For any morphism `r : X₂ ⟶ X₄` in `TopCat.{u}`, the inverse image of the complement of its image is empty:
`r ⁻¹' ((Set.range r.hom)ᶜ) = ∅`. -/
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

/-- Let `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶ X₄`, and `b : X₃ ⟶ X₄` form a pushout in `TopCat.{u}`. Then
`b ⁻¹' ((Set.range r.hom)ᶜ) ⊆ (Set.range l.hom)ᶜ`:
a point of `X₃` mapping outside the image of `r` lies outside the image of `l`. -/
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

/-- For a pushout `IsPushout t l r b` in `TopCat.{u}`, with `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r : X₂ ⟶ X₄`, and `b : X₃ ⟶ X₄`,
`b ⁻¹' ((Set.range r.hom)ᶜ) = (Set.range l.hom)ᶜ`.
Thus the points of the new leg outside the attaching image are exactly those whose pushout images avoid the old leg. -/
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

/-- Let `IsPushout t l r b` be a pushout in `TopCat.{u}`, where `t : X₁ ⟶ X₂`, `l : X₁ ⟶ X₃`, `r :
X₂ ⟶ X₄`, and `b : X₃ ⟶ X₄`. If `r.hom` is a closed embedding and `U = (Set.range r.hom)ᶜ`,
then `U.restrictPreimage b : b ⁻¹' U → U` is a homeomorphism for the subspace topologies. -/
theorem isHomeomorph_oneCellOpenComplement_restrictPreimage
    (sq : IsPushout t l r b) (hr_closed : IsClosedEmbedding r.hom) :
    IsHomeomorph (((Set.range r.hom)ᶜ).restrictPreimage b) := by
  exact isHomeomorph_restrictPreimage_inr_of_isPushout sq
    (isOpen_oneCellOpenComplement hr_closed)
    preimage_oneCellOpenComplement_self
    (preimage_oneCellOpenComplement_subset sq)

end TopCat
