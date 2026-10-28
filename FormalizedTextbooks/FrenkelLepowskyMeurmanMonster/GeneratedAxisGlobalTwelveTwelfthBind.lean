/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentBridge
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthPhase

/-! # Binding Twelfth root vectors from identification equations

`twelfthRootX k` is the image of the Twelfth axis under the identification word of Twelfth root
`k`. The lemmas below turn identification equations, in the form produced by the packed
identification method, into memberships of the two triality images of `twelfthRootX k` in the
union of the twelve local orbits:

* the Twelfth vector as source: `twelfthRoot_pos_of_src`, `twelfthRoot_neg_of_src`;
* the Twelfth vector as target behind an Xi-free prefix `M` (phase read off from the Q-phase of
  `M`): `twelfthRoot_of_target_forward`, `twelfthRoot_of_target_inverse`;
* the other image of a source vector through the partner vertex of the same triality triangle:
  `twelfthRoot_neg_of_src_fix`, `twelfthRoot_neg_of_src_flip`, `twelfthRoot_pos_of_srcInv_fix`,
  `twelfthRoot_pos_of_srcInv_flip` (the partner image is an explicit hypothesis).

All statements are conditional on the displayed equations; no identification is asserted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The image of the Twelfth axis under the identification word of Twelfth root `k`. -/
def twelfthRootX (k : Fin 38) : GriessSpace :=
  rhoLocal (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord k)) generatedTwelfthAxis

/-- The Twelfth axis is family representative `10`. -/
theorem twelfthRep_eq : generatedAxisGlobalTwelveRepresentative 10 = generatedTwelfthAxis := rfl

/-- A forward identification with the Twelfth root vector as source binds its positive image. -/
theorem twelfthRoot_pos_of_src (k : Fin 38) (j : Fin 12) (g : H)
    (he : sExtra (twelfthRootX k) = rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) :
    sExtra (twelfthRootX k) ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport j g he

/-- An inverse identification with the Twelfth root vector as source binds its inverse image. -/
theorem twelfthRoot_neg_of_src (k : Fin 38) (j : Fin 12) (g : H)
    (he : sExtra⁻¹ (twelfthRootX k) = rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) :
    sExtra⁻¹ (twelfthRootX k) ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport j g he

/-- A forward identification landing on `M · r_k · v₁₂` binds one image of the Twelfth root vector,
of the sign given by the Q-phase of the Xi-free prefix `M`. -/
theorem twelfthRoot_of_target_forward (k : Fin 38) (i : Fin 12) (h : H) (M : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (he : sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal (identWordLocal (M ++ generatedAxisGlobalTwelveTwelfthRootIdentWord k))
        generatedTwelfthAxis) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra⁻¹ (twelfthRootX k) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra (twelfthRootX k) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :=
  sixthPhase_of_forward_identity i h M _ hM hxi _ he

/-- An inverse identification landing on `M · r_k · v₁₂` binds one image of the Twelfth root vector,
of the sign given by the Q-phase of the Xi-free prefix `M`. -/
theorem twelfthRoot_of_target_inverse (k : Fin 38) (i : Fin 12) (h : H) (M : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (he : sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal (identWordLocal (M ++ generatedAxisGlobalTwelveTwelfthRootIdentWord k))
        generatedTwelfthAxis) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra (twelfthRootX k) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra⁻¹ (twelfthRootX k) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :=
  sixthPhase_of_inverse_identity i h M _ hM hxi _ he

private theorem twelfth_inv_eq_sq (y : GriessSpace) : sExtra⁻¹ y = sExtra (sExtra y) := by
  apply sExtra.injective
  rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

private theorem twelfth_eq_inv_sq (y : GriessSpace) : sExtra y = sExtra⁻¹ (sExtra⁻¹ y) := by
  rw [twelfth_inv_eq_sq (sExtra⁻¹ y), LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- A positive image in an Ω-fixing coset: the prefix may be removed or added. -/
theorem twelfth_forward_add_mem (n r : H) (v : GriessSpace) (hn : n ∈ localOmegaStabilizer)
    (hmem : sExtra (rhoLocal r v) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (n * r) v) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  apply sixthPhase_forward_of_mem _ n⁻¹ _ v (inv_mem hn)
  rw [inv_mul_cancel_left]
  exact hmem

/-- An inverse image in an Ω-fixing coset: the prefix may be added. -/
theorem twelfth_inverse_add_mem (n r : H) (v : GriessSpace) (hn : n ∈ localOmegaStabilizer)
    (hmem : sExtra⁻¹ (rhoLocal r v) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra⁻¹ (rhoLocal (n * r) v) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  apply sixthPhase_inverse_of_mem _ n⁻¹ _ v (inv_mem hn)
  rw [inv_mul_cancel_left]
  exact hmem

/-- From `sExtra x = (M ++ T) · v` with an Ω-fixing prefix and the positive image of `T · v`, the
inverse image of `x` is bound. -/
theorem twelfthRoot_neg_of_src_fix (k : Fin 38) (M T : List IdentLetter) (v : GriessSpace)
    (hM : ∀ l ∈ M, SixthPhaseLetter l)
    (hfix : qmWord (M.map sixthPhaseData) (2048, false) = (2048, false))
    (he : sExtra (twelfthRootX k) = rhoLocal (identWordLocal (M ++ T)) v)
    (hT : sExtra (rhoLocal (identWordLocal T) v) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra⁻¹ (twelfthRootX k) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [twelfth_inv_eq_sq, he, identWordLocal_append]
  exact twelfth_forward_add_mem _ _ v (sixthPhase_mem M hM hfix) hT

/-- From `sExtra x = (M ++ T) · v` with an Ω-flipping Xi-free prefix and the inverse image of
`T · v`, the inverse image of `x` is bound. -/
theorem twelfthRoot_neg_of_src_flip (k : Fin 38) (M T : List IdentLetter) (v : GriessSpace)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi)
    (hflip : qmWord (M.map sixthPhaseData) (2048, false) = (2048, true))
    (he : sExtra (twelfthRootX k) = rhoLocal (identWordLocal (M ++ T)) v)
    (hT : sExtra⁻¹ (rhoLocal (identWordLocal T) v) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra⁻¹ (twelfthRootX k) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [twelfth_inv_eq_sq, he, identWordLocal_append]
  have hn := sixthPhase_flip_mem M hM hxi hflip
  have e : identWordLocal M * identWordLocal T =
      (identWordLocal M * inclQ singletonCocodeQ) *
        (inclQ singletonCocodeQ * identWordLocal T) := by
    rw [mul_assoc, ← mul_assoc (inclQ singletonCocodeQ), ← map_mul]
    change _ = identWordLocal M * (inclQ (cocodeQ _ * cocodeQ _) * identWordLocal T)
    rw [cocodeQ_square, map_one, one_mul]
  rw [e]
  apply twelfth_forward_add_mem _ _ v hn
  rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
  have hsq : inclQ singletonCocodeQ * inclQ singletonCocodeQ = (1 : H) := by
    rw [← map_mul]
    change inclQ (cocodeQ _ * cocodeQ _) = 1
    rw [cocodeQ_square, map_one]
  have hc : rhoLocal (inclQ singletonCocodeQ) (rhoLocal (inclQ singletonCocodeQ)
      (sExtra⁻¹ (rhoLocal (identWordLocal T) v))) = sExtra⁻¹ (rhoLocal (identWordLocal T) v) := by
    rw [← LinearEquiv.mul_apply, ← map_mul, hsq, map_one, LinearEquiv.coe_one, id_eq]
  exact generatedAxisGlobalTwelve_union_mem_of_local _ (inclQ singletonCocodeQ) hT hc.symm

/-- From `sExtra⁻¹ x = (M ++ T) · v` with an Ω-fixing prefix and the inverse image of `T · v`, the
positive image of `x` is bound. -/
theorem twelfthRoot_pos_of_srcInv_fix (k : Fin 38) (M T : List IdentLetter) (v : GriessSpace)
    (hM : ∀ l ∈ M, SixthPhaseLetter l)
    (hfix : qmWord (M.map sixthPhaseData) (2048, false) = (2048, false))
    (he : sExtra⁻¹ (twelfthRootX k) = rhoLocal (identWordLocal (M ++ T)) v)
    (hT : sExtra⁻¹ (rhoLocal (identWordLocal T) v) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (twelfthRootX k) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [twelfth_eq_inv_sq, he, identWordLocal_append]
  exact twelfth_inverse_add_mem _ _ v (sixthPhase_mem M hM hfix) hT

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
