/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhPairs

/-! Triality triangles and phase-free triangle closure.

Triality has order three, so a vector `x` lies in the triangle `{x, sExtra x, sExtra⁻¹ x}`, which
contains both triality images of each of its vertices. If a vertex is written `(M ++ T) · v`
with an Xi-free identification prefix `M`, the prefix lies in the local Ω stabilizer up to the
singleton cocode element; in both cases the two triality images of `T · v` are those of the vertex
(possibly exchanged). Hence: if both images of `x` lie in the catalogue union, so do both images
of `T · v`; and if both images of `T · v` lie in the union, so do both images of `x`. Two
identifications therefore bind a whole triangle, without computing any phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- The inverse triality is the square of triality. -/
theorem sixthTri_inv_eq_sq (y : GriessSpace) : sExtra⁻¹ y = sExtra (sExtra y) := by
  have h := sExtra_triple (sExtra⁻¹ y)
  rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h
  rw [LinearEquiv.coe_inv, ← h]

/-- The inverse triality twice is triality. -/
theorem sixthTri_inv_inv (y : GriessSpace) : sExtra⁻¹ (sExtra⁻¹ y) = sExtra y := by
  rw [sixthTri_inv_eq_sq (sExtra⁻¹ y), LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

private theorem sixthTri_square :
    inclQ singletonCocodeQ * inclQ singletonCocodeQ = (1 : H) := by
  rw [← map_mul]
  change inclQ (cocodeQ _ * cocodeQ _) = 1
  rw [cocodeQ_square, map_one]

/-- A local Ω stabilizer prefix keeps the positive image in a local orbit union. -/
theorem sixthTri_forward_mem_of_mem {ι : Type*} (u : ι → GriessSpace) (n r : H)
    (v : GriessSpace) (hn : n ∈ localOmegaStabilizer)
    (h : sExtra (rhoLocal r v) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal (n * r) v) ∈ generatedLocalOrbitUnion u := by
  obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩ (rhoLocal r v)
  rw [map_mul, LinearEquiv.mul_apply, ← hk]
  exact generatedLocalOrbitUnion_local u k h

/-- A local Ω stabilizer prefix keeps the inverse image in a local orbit union. -/
theorem sixthTri_inverse_mem_of_mem {ι : Type*} (u : ι → GriessSpace) (n r : H)
    (v : GriessSpace) (hn : n ∈ localOmegaStabilizer)
    (h : sExtra⁻¹ (rhoLocal r v) ∈ generatedLocalOrbitUnion u) :
    sExtra⁻¹ (rhoLocal (n * r) v) ∈ generatedLocalOrbitUnion u := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalTwelve_omega_inverse_orbit ⟨n, hn⟩ (rhoLocal r v)
  rw [map_mul, LinearEquiv.mul_apply, ← hk]
  exact generatedLocalOrbitUnion_local u k h

/-- A flipped prefix takes the inverse image to the positive image. -/
theorem sixthTri_forward_mem_of_flip {ι : Type*} (u : ι → GriessSpace) (n r : H)
    (v : GriessSpace) (hn : n * inclQ singletonCocodeQ ∈ localOmegaStabilizer)
    (h : sExtra⁻¹ (rhoLocal r v) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal (n * r) v) ∈ generatedLocalOrbitUnion u := by
  have he : n * r = (n * inclQ singletonCocodeQ) * (inclQ singletonCocodeQ * r) := by
    rw [mul_assoc, ← mul_assoc (inclQ singletonCocodeQ), sixthTri_square, one_mul]
  rw [he]
  apply sixthTri_forward_mem_of_mem u _ _ v hn
  rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
  exact generatedLocalOrbitUnion_local u _ h

/-- A flipped prefix takes the positive image to the inverse image. -/
theorem sixthTri_inverse_mem_of_flip {ι : Type*} (u : ι → GriessSpace) (n r : H)
    (v : GriessSpace) (hn : n * inclQ singletonCocodeQ ∈ localOmegaStabilizer)
    (h : sExtra (rhoLocal r v) ∈ generatedLocalOrbitUnion u) :
    sExtra⁻¹ (rhoLocal (n * r) v) ∈ generatedLocalOrbitUnion u := by
  have he : n * r = (n * inclQ singletonCocodeQ) * (inclQ singletonCocodeQ * r) := by
    rw [mul_assoc, ← mul_assoc (inclQ singletonCocodeQ), sixthTri_square, one_mul]
  rw [he]
  apply sixthTri_inverse_mem_of_mem u _ _ v hn
  rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobalTwelve_singleton_inverse_exchange]
  exact generatedLocalOrbitUnion_local u _ h

/-- A frame-fixing prefix exchanges or keeps the two triality images: if both images of
`(n * r) · v` lie in a local orbit union, so do both images of `r · v`. -/
theorem sixthTri_both_of_prefix {ι : Type*} (u : ι → GriessSpace) (n r : H) (v : GriessSpace)
    (hn : projH n ∈ co1OmegaFrameStabilizer)
    (hp : sExtra (rhoLocal (n * r) v) ∈ generatedLocalOrbitUnion u)
    (hm : sExtra⁻¹ (rhoLocal (n * r) v) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal r v) ∈ generatedLocalOrbitUnion u ∧
      sExtra⁻¹ (rhoLocal r v) ∈ generatedLocalOrbitUnion u := by
  rcases generatedAxisGlobal_binary_normalizer_split n hn with h0 | h1
  · exact ⟨sixthPhase_forward_of_mem u n r v h0 hp, sixthPhase_inverse_of_mem u n r v h0 hm⟩
  · exact ⟨sixthPhase_inverse_of_flip u n r v h1 hm, sixthPhase_forward_of_flip u n r v h1 hp⟩

/-- Conversely, if both images of `r · v` lie in a local orbit union, so do both images of
`(n * r) · v`, for a frame-fixing prefix `n`. -/
theorem sixthTri_prefix_of_both {ι : Type*} (u : ι → GriessSpace) (n r : H) (v : GriessSpace)
    (hn : projH n ∈ co1OmegaFrameStabilizer)
    (hp : sExtra (rhoLocal r v) ∈ generatedLocalOrbitUnion u)
    (hm : sExtra⁻¹ (rhoLocal r v) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal (n * r) v) ∈ generatedLocalOrbitUnion u ∧
      sExtra⁻¹ (rhoLocal (n * r) v) ∈ generatedLocalOrbitUnion u := by
  rcases generatedAxisGlobal_binary_normalizer_split n hn with h0 | h1
  · exact ⟨sixthTri_forward_mem_of_mem u n r v h0 hp, sixthTri_inverse_mem_of_mem u n r v h0 hm⟩
  · exact ⟨sixthTri_forward_mem_of_flip u n r v h1 hm, sixthTri_inverse_mem_of_flip u n r v h1 hp⟩

/-- Both images of a vertex of the triangle of `x`, when both images of `x` are known and `x`
itself lies in the union. -/
theorem sixthTri_vertex_both {ι : Type*} (u : ι → GriessSpace) (x z : GriessSpace)
    (hx : x ∈ generatedLocalOrbitUnion u) (hp : sExtra x ∈ generatedLocalOrbitUnion u)
    (hm : sExtra⁻¹ x ∈ generatedLocalOrbitUnion u) (hz : z = sExtra x ∨ z = sExtra⁻¹ x) :
    sExtra z ∈ generatedLocalOrbitUnion u ∧ sExtra⁻¹ z ∈ generatedLocalOrbitUnion u := by
  rcases hz with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [← sixthTri_inv_eq_sq]
      exact hm
    · rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
      exact hx
  · refine ⟨?_, ?_⟩
    · rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
      exact hx
    · rw [sixthTri_inv_inv]
      exact hp

/-- Triangle closure (forward): if both images of `x` (and `x`) lie in the catalogue union and
a triangle vertex of `x` is `(M ++ T) · v` with an Xi-free prefix `M`, both images of `T · v`
lie in the union. -/
theorem sixthTri_target_both (x : GriessSpace) (M T : List IdentLetter)
    (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi) (v : GriessSpace)
    (hx : x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hp : sExtra x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hm : sExtra⁻¹ x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (he : sExtra x = rhoLocal (identWordLocal (M ++ T)) v ∨
      sExtra⁻¹ x = rhoLocal (identWordLocal (M ++ T)) v) :
    sExtra (rhoLocal (identWordLocal T) v) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (identWordLocal T) v) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hz := sixthTri_vertex_both _ x _ hx hp hm (he.imp Eq.symm Eq.symm)
  rw [identWordLocal_append] at hz
  exact sixthTri_both_of_prefix _ _ _ v (sixthFrame_identWord M hxi) hz.1 hz.2

/-- Triangle closure (backward): if both images of `T · v_j` lie in the catalogue union and a
triangle vertex of `x` is `(M ++ T) · v_j` with an Xi-free prefix `M`, both images of `x` lie in
the union. -/
theorem sixthTri_source_both (x : GriessSpace) (M T : List IdentLetter)
    (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi) (j : Fin 12)
    (hp : sExtra (rhoLocal (identWordLocal T) (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hm : sExtra⁻¹ (rhoLocal (identWordLocal T) (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (he : sExtra x =
        rhoLocal (identWordLocal (M ++ T)) (generatedAxisGlobalTwelveRepresentative j) ∨
      sExtra⁻¹ x =
        rhoLocal (identWordLocal (M ++ T)) (generatedAxisGlobalTwelveRepresentative j)) :
    sExtra x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hb := sixthTri_prefix_of_both _ (identWordLocal M) _ _ (sixthFrame_identWord M hxi) hp hm
  rw [← identWordLocal_append] at hb
  rcases he with he | he
  · refine ⟨he ▸ ⟨j, _, rfl⟩, ?_⟩
    rw [sixthTri_inv_eq_sq, he]
    exact hb.1
  · refine ⟨?_, he ▸ ⟨j, _, rfl⟩⟩
    rw [← sixthTri_inv_inv, he]
    exact hb.2

/-! ## The internal Sixth/Seventh triangles -/

/-- Triangle `{Sixth i, Seventh i', ·}`: an inverse Sixth identification landing on a Seventh cell
and the positive image of the Sixth cell bind both images of the Seventh cell. -/
theorem seventhCell_both_of_sixth_neg (i : Fin 10) (i' : Fin 23) (M : List IdentLetter)
    (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi) (h : SixthCellIdentNeg i 6 (M ++ seventhCellIdent i'))
    (hp : sExtra (rhoLocal (sixthCellWord i) generatedSixthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (seventhCellWord i') generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (seventhCellWord i') generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [seventhCellWord_ident]
  rw [sixthCellWord_ident] at hp
  exact sixthTri_target_both _ M _ hxi _ ⟨5, _, rfl⟩ hp
    (generatedAxisGlobalTwelve_mem_of_transport 6 _ h) (Or.inr h)

/-- Triangle `{Seventh i, Sixth i', ·}`: an inverse Seventh identification landing on a Sixth cell
and the positive image of the Seventh cell bind both images of the Sixth cell. -/
theorem sixthCell_both_of_seventh_neg (i : Fin 23) (i' : Fin 10) (M : List IdentLetter)
    (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi) (h : SeventhCellIdentNeg i 5 (M ++ sixthCellIdent i'))
    (hp : sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (sixthCellWord i') generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (sixthCellWord i') generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [sixthCellWord_ident]
  rw [seventhCellWord_ident] at hp
  exact sixthTri_target_both _ M _ hxi _ ⟨6, _, rfl⟩ hp
    (generatedAxisGlobalTwelve_mem_of_transport 5 _ h) (Or.inr h)

/-- Triangle `{Seventh i, Seventh i', ·}`: an inverse Seventh identification landing on a Seventh
cell and the positive image of the first cell bind both images of the second cell. -/
theorem seventhCell_both_of_seventh_neg (i i' : Fin 23) (M : List IdentLetter)
    (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi) (h : SeventhCellIdentNeg i 6 (M ++ seventhCellIdent i'))
    (hp : sExtra (rhoLocal (seventhCellWord i) generatedSeventhAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (seventhCellWord i') generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (seventhCellWord i') generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [seventhCellWord_ident]
  rw [seventhCellWord_ident] at hp
  exact sixthTri_target_both _ M _ hxi _ ⟨6, _, rfl⟩ hp
    (generatedAxisGlobalTwelve_mem_of_transport 6 _ h) (Or.inr h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
