/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBind

/-! # Phase transfer in both directions and partner vertices of identifications

For an Xi-free prefix `M` of qualifying letters, the Q-phase of `M` decides whether `M` fixes the
Ω-mask (`(2048, false)`) or flips it (`(2048, true)`).  A fixing prefix preserves each triality
image of a vector in the union of the twelve local orbits, a flipping prefix exchanges the two
images (`twelfth_fwd_iff_fix`, `twelfth_inv_iff_fix`, `twelfth_fwd_iff_flip`,
`twelfth_inv_iff_flip`, both directions).

An identification `sExtra^{±1} Y = (M ++ T) · v` relates the two triality triangles of `Y` and of
`T · v`: besides the two vertices bound directly, the remaining image of `Y` is bound exactly when
the remaining image of `T · v` is (`twelfth_partner_forward`, `twelfth_partner_inverse`).  All
statements are conditional on the displayed equations; no identification is asserted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem partner_singleton_sq :
    inclQ singletonCocodeQ * inclQ singletonCocodeQ = (1 : H) := by
  rw [← map_mul]
  change inclQ (cocodeQ _ * cocodeQ _) = 1
  rw [cocodeQ_square, map_one]

private theorem partner_inv_eq_sq (y : GriessSpace) : sExtra⁻¹ y = sExtra (sExtra y) := by
  apply sExtra.injective
  rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

private theorem partner_eq_inv_sq (y : GriessSpace) : sExtra y = sExtra⁻¹ (sExtra⁻¹ y) := by
  rw [partner_inv_eq_sq (sExtra⁻¹ y), LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

private theorem partner_split (M : List IdentLetter) (r : H) :
    identWordLocal M * r =
      (identWordLocal M * inclQ singletonCocodeQ) * (inclQ singletonCocodeQ * r) := by
  rw [mul_assoc, ← mul_assoc (inclQ singletonCocodeQ), partner_singleton_sq, one_mul]

/-- An Ω-fixing prefix preserves the positive image (both directions). -/
theorem twelfth_fwd_iff_fix (M : List IdentLetter) (hM : ∀ l ∈ M, SixthPhaseLetter l)
    (hfix : qmWord (M.map sixthPhaseData) (2048, false) = (2048, false)) (r : H)
    (v : GriessSpace) :
    sExtra (rhoLocal (identWordLocal M * r) v) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra (rhoLocal r v) ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨sixthPhase_forward_of_mem _ _ r v (sixthPhase_mem M hM hfix),
    twelfth_forward_add_mem _ r v (sixthPhase_mem M hM hfix)⟩

/-- An Ω-fixing prefix preserves the inverse image (both directions). -/
theorem twelfth_inv_iff_fix (M : List IdentLetter) (hM : ∀ l ∈ M, SixthPhaseLetter l)
    (hfix : qmWord (M.map sixthPhaseData) (2048, false) = (2048, false)) (r : H)
    (v : GriessSpace) :
    sExtra⁻¹ (rhoLocal (identWordLocal M * r) v) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra⁻¹ (rhoLocal r v) ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨sixthPhase_inverse_of_mem _ _ r v (sixthPhase_mem M hM hfix),
    twelfth_inverse_add_mem _ r v (sixthPhase_mem M hM hfix)⟩

/-- An Ω-flipping Xi-free prefix exchanges the positive image for the inverse one. -/
theorem twelfth_fwd_iff_flip (M : List IdentLetter) (hM : ∀ l ∈ M, SixthPhaseLetter l)
    (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (hflip : qmWord (M.map sixthPhaseData) (2048, false) = (2048, true)) (r : H)
    (v : GriessSpace) :
    sExtra (rhoLocal (identWordLocal M * r) v) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra⁻¹ (rhoLocal r v) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hn := sixthPhase_flip_mem M hM hxi hflip
  refine ⟨sixthPhase_forward_of_flip _ _ r v hn, fun h => ?_⟩
  rw [partner_split M r]
  apply twelfth_forward_add_mem _ _ v hn
  rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
  exact generatedLocalOrbitUnion_local _ _ h

/-- An Ω-flipping Xi-free prefix exchanges the inverse image for the positive one. -/
theorem twelfth_inv_iff_flip (M : List IdentLetter) (hM : ∀ l ∈ M, SixthPhaseLetter l)
    (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (hflip : qmWord (M.map sixthPhaseData) (2048, false) = (2048, true)) (r : H)
    (v : GriessSpace) :
    sExtra⁻¹ (rhoLocal (identWordLocal M * r) v) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra (rhoLocal r v) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hn := sixthPhase_flip_mem M hM hxi hflip
  refine ⟨sixthPhase_inverse_of_flip _ _ r v hn, fun h => ?_⟩
  rw [partner_split M r]
  apply twelfth_inverse_add_mem _ _ v hn
  rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobalTwelve_singleton_inverse_exchange]
  exact generatedLocalOrbitUnion_local _ _ h

/-- Partner vertex of a forward identification `sExtra Y = (M ++ T) · v`: the inverse image of
`Y` is bound exactly when the image of `T · v` of the sign given by the phase of `M` is. -/
theorem twelfth_partner_forward (Y : GriessSpace) (M T : List IdentLetter) (v : GriessSpace)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (he : sExtra Y = rhoLocal (identWordLocal (M ++ T)) v) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      (sExtra⁻¹ Y ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
        sExtra (rhoLocal (identWordLocal T) v) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      (sExtra⁻¹ Y ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
        sExtra⁻¹ (rhoLocal (identWordLocal T) v) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)) := by
  have hY : sExtra⁻¹ Y = sExtra (rhoLocal (identWordLocal M * identWordLocal T) v) := by
    rw [partner_inv_eq_sq, he, identWordLocal_append]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hY]
    exact twelfth_fwd_iff_fix M hM h _ v
  · rw [hY]
    exact twelfth_fwd_iff_flip M hM hxi h _ v

/-- Partner vertex of an inverse identification `sExtra⁻¹ Y = (M ++ T) · v`: the positive image
of `Y` is bound exactly when the image of `T · v` of the sign given by the phase of `M` is. -/
theorem twelfth_partner_inverse (Y : GriessSpace) (M T : List IdentLetter) (v : GriessSpace)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (he : sExtra⁻¹ Y = rhoLocal (identWordLocal (M ++ T)) v) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      (sExtra Y ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
        sExtra⁻¹ (rhoLocal (identWordLocal T) v) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      (sExtra Y ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
        sExtra (rhoLocal (identWordLocal T) v) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)) := by
  have hY : sExtra Y = sExtra⁻¹ (rhoLocal (identWordLocal M * identWordLocal T) v) := by
    rw [partner_eq_inv_sq, he, identWordLocal_append]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hY]
    exact twelfth_inv_iff_fix M hM h _ v
  · rw [hY]
    exact twelfth_inv_iff_flip M hM hxi h _ v

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
