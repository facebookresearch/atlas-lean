/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthFamily

/-! Generic links from explicit whole transports to Twelfth root bindings.

* A whole transport of any listed family into the Twelfth orbit gives both triality images at
  the target coset (`generatedAxisGlobalTwelveTwelfth_pair_of_forward_transport` and its inverse
  version).
* A target coset `n * rootWord k` with `n` fixing the binary Ω point has the binary root of
  `rootWord k`, so a binding there binds the root word (`..._root_pair_of_frame`).
* A self-transport `sExtra x = n x` (or `sExtra⁻¹ x = n x`) by an element `n` of the actual
  Ω stabilizer forces the other triality image into the orbit of `x` as well
  (`..._other_sign_of_omega_forward`, `..._other_sign_of_omega_inverse`).
All statements are conditional only on the displayed transports; no transport is asserted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem sExtra_inv_eq_square_twelfth (y : GriessSpace) :
    sExtra⁻¹ y = sExtra (sExtra y) := by
  apply sExtra.injective
  rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- A forward whole transport into the Twelfth orbit gives both images at the target coset. -/
theorem generatedAxisGlobalTwelveTwelfth_pair_of_forward_transport (j : Fin 12) (x h : H)
    (htrans : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) =
      rhoLocal h generatedTwelfthAxis)
    (hsrc : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal h generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal h generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [← htrans]
  refine ⟨?_, ?_⟩
  · rw [← sExtra_inv_eq_square_twelfth]
    exact hsrc
  · rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact generatedAxisGlobalTwelve_mem_of_transport j x rfl

/-- An inverse whole transport into the Twelfth orbit gives both images at the target coset. -/
theorem generatedAxisGlobalTwelveTwelfth_pair_of_inverse_transport (j : Fin 12) (x h : H)
    (htrans : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) =
      rhoLocal h generatedTwelfthAxis)
    (hsrc : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal h generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal h generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [← htrans]
  refine ⟨?_, ?_⟩
  · rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    exact generatedAxisGlobalTwelve_mem_of_transport j x rfl
  · have e : sExtra⁻¹ (sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j))) =
        sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) := by
      rw [sExtra_inv_eq_square_twelfth (sExtra⁻¹ _), LinearEquiv.coe_inv,
        LinearEquiv.apply_symm_apply]
    rw [e]
    exact hsrc

/-- An element fixing the binary Ω point does not change binary roots. -/
theorem generatedAxisGlobalTwelveTwelfth_binaryRoot_frame (n r : H)
    (hn : projH n ∈ co1OmegaFrameStabilizer) :
    generatedAxisGlobalBinaryRoot (n * r) = generatedAxisGlobalBinaryRoot r := by
  apply Subtype.ext
  change co1BinaryAction (projH (n * r)⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) =
    co1BinaryAction (projH r⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ))
  have hn' : co1BinaryAction (projH n⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) =
      Multiplicative.toAdd (qQuotHom sourceOmegaQ) := by
    have h1 := (co1OmegaFrameStabilizer.inv_mem hn)
    rw [← map_inv] at h1
    exact h1
  rw [mul_inv_rev, map_mul, map_mul, LinearEquiv.mul_apply, hn']

/-- A binding at a coset `n * rootWord k` with `n` fixing the binary Ω point binds root word `k`. -/
theorem generatedAxisGlobalTwelveTwelfth_root_pair_of_frame {ι : Type*} (u : ι → GriessSpace)
    (k : Fin 38) (n : H) (hn : projH n ∈ co1OmegaFrameStabilizer)
    (hpos : sExtra (rhoLocal (n * generatedAxisGlobalTwelveTwelfthRootWord k)
      generatedTwelfthAxis) ∈ generatedLocalOrbitUnion u)
    (hneg : sExtra⁻¹ (rhoLocal (n * generatedAxisGlobalTwelveTwelfthRootWord k)
      generatedTwelfthAxis) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion u ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveTwelfthRootWord k) generatedTwelfthAxis) ∈
        generatedLocalOrbitUnion u := by
  apply generatedAxisGlobalTwelve_root_pair_mem u generatedTwelfthAxis
    (n * generatedAxisGlobalTwelveTwelfthRootWord k) (generatedAxisGlobalTwelveTwelfthRootWord k) 1
    (by rw [map_one, LinearEquiv.coe_one, id_eq]) _ hpos hneg
  rw [generatedAxisGlobalTwelveTwelfth_binaryRoot_frame n _ hn]
  apply Subtype.ext
  change co1BinaryAction (projH 1) _ = _
  rw [map_one, map_one]
  rfl

/-- A forward self-transport by an actual Ω-stabilizer element also binds the inverse image. -/
theorem generatedAxisGlobalTwelveTwelfth_other_sign_of_omega_forward (x : GriessSpace) (n : H)
    (hn : n ∈ localOmegaStabilizer) (htrans : sExtra x = rhoLocal n x) :
    ∃ m : H, sExtra⁻¹ x = rhoLocal m x := by
  obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩ x
  refine ⟨k * n, ?_⟩
  rw [sExtra_inv_eq_square_twelfth, htrans, ← hk, htrans, map_mul, LinearEquiv.mul_apply]

/-- An inverse self-transport by an actual Ω-stabilizer element also binds the forward image. -/
theorem generatedAxisGlobalTwelveTwelfth_other_sign_of_omega_inverse (x : GriessSpace) (n : H)
    (hn : n ∈ localOmegaStabilizer) (htrans : sExtra⁻¹ x = rhoLocal n x) :
    ∃ m : H, sExtra x = rhoLocal m x := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalTwelve_omega_inverse_orbit ⟨n, hn⟩ x
  refine ⟨k * n, ?_⟩
  have e : sExtra x = sExtra⁻¹ (sExtra⁻¹ x) := by
    rw [sExtra_inv_eq_square_twelfth (sExtra⁻¹ x), LinearEquiv.coe_inv,
      LinearEquiv.apply_symm_apply]
  rw [e, htrans, ← hk, htrans, map_mul, LinearEquiv.mul_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
