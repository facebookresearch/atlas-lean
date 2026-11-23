/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.PushoutOpenComplement

/-!
# Actual images of regions away from an attaching boundary

In a topological pushout, a region of the first attached space that avoids
the attaching boundary has no identifications with the original space.
Its actual image has the original region as its first preimage and an
empty second preimage. Openness and closedness therefore descend through
the canonical quotient map. These formulas construct the radial regions
used by cell-attachment collar covers.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits Topology

universe u

namespace TopCat

variable {A B X Y : TopCat.{u}}
variable {i : A ⟶ B} {g : A ⟶ X} {r : B ⟶ Y} {j : X ⟶ Y}

/-- An actual attached region away from the boundary has exactly its original first preimage. -/
theorem preimage_left_image_left_of_avoids_boundary
    (h : IsPushout i g r j) {S : Set B} (hS : S ⊆ (Set.range i)ᶜ) :
    r ⁻¹' (r '' S) = S := by
  ext b
  constructor
  · rintro ⟨s, hs, hsb⟩
    have heq := Types.pushoutCocone_inr_eq_inr_of_not_mem_range_of_isColimit
      (h.flip.map (forget TopCat)).isColimit (hS hs) hsb
    change s = b at heq
    exact heq ▸ hs
  · intro hb
    exact ⟨b, hb, rfl⟩

/-- The actual image of a region away from the boundary has no original-source preimage. -/
theorem preimage_right_image_left_of_avoids_boundary
    (h : IsPushout i g r j) {S : Set B} (hS : S ⊆ (Set.range i)ᶜ) :
    j ⁻¹' (r '' S) = ∅ := by
  ext x
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hne := Types.pushoutCocone_inl_ne_inr_of_not_mem_range_of_isColimit
      (h.flip.map (forget TopCat)).isColimit (z := x) (hS hs)
    exact (hne hsx.symm).elim
  · intro hx
    exact hx.elim

/-- The actual image of an open attached region away from the boundary is open in the pushout. -/
theorem isOpen_image_left_of_avoids_boundary
    (h : IsPushout i g r j) {S : Set B} (hS : S ⊆ (Set.range i)ᶜ) (hs : IsOpen S) :
    IsOpen (r '' S) := by
  apply (isQuotientMap_sumElim_of_isPushout h).isOpen_preimage.mp
  rw [isOpen_sum_iff]
  change IsOpen (r ⁻¹' (r '' S)) ∧ IsOpen (j ⁻¹' (r '' S))
  rw [preimage_left_image_left_of_avoids_boundary h hS,
    preimage_right_image_left_of_avoids_boundary h hS]
  exact ⟨hs, isOpen_empty⟩

/-- The actual image of a closed attached region away from the boundary is closed in the pushout. -/
theorem isClosed_image_left_of_avoids_boundary
    (h : IsPushout i g r j) {S : Set B} (hS : S ⊆ (Set.range i)ᶜ) (hs : IsClosed S) :
    IsClosed (r '' S) := by
  apply (isQuotientMap_sumElim_of_isPushout h).isClosed_preimage.mp
  rw [isClosed_sum_iff]
  change IsClosed (r ⁻¹' (r '' S)) ∧ IsClosed (j ⁻¹' (r '' S))
  rw [preimage_left_image_left_of_avoids_boundary h hS,
    preimage_right_image_left_of_avoids_boundary h hS]
  exact ⟨hs, isClosed_empty⟩

/-- The original-source leg lands entirely in the complement of the actual closed core image. -/
theorem preimage_right_compl_image_left_of_avoids_boundary
    (h : IsPushout i g r j) {S : Set B} (hS : S ⊆ (Set.range i)ᶜ) :
    j ⁻¹' (r '' S)ᶜ = Set.univ := by
  rw [Set.preimage_compl, preimage_right_image_left_of_avoids_boundary h hS,
    Set.compl_empty]

/-- The attached-space preimage of the complement of the actual core image
is its original complement. -/
theorem preimage_left_compl_image_left_of_avoids_boundary
    (h : IsPushout i g r j) {S : Set B} (hS : S ⊆ (Set.range i)ᶜ) :
    r ⁻¹' (r '' S)ᶜ = Sᶜ := by
  rw [Set.preimage_compl, preimage_left_image_left_of_avoids_boundary h hS]

/-- Restricting to the actual image of an open boundary-free region is a homeomorphism. -/
theorem isHomeomorph_restrictPreimage_left_image_of_avoids_boundary
    (h : IsPushout i g r j) {S : Set B} (hS : S ⊆ (Set.range i)ᶜ) (hs : IsOpen S) :
    IsHomeomorph ((r '' S).restrictPreimage r) := by
  apply isHomeomorph_restrictPreimage_inr_of_isPushout h.flip
    (isOpen_image_left_of_avoids_boundary h hS hs)
    (preimage_right_image_left_of_avoids_boundary h hS)
  rw [preimage_left_image_left_of_avoids_boundary h hS]
  exact hS

end TopCat
