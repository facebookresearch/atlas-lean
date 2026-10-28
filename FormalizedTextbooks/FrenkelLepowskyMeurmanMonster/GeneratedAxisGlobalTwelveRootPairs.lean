/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary

/-! Sign-paired transport of actual triality transitions along a binary root relation.

If an actual stabilizer element carries the binary root of `r` to the binary root of `h`,
then the two triality images at `h` are, as a pair, local images of the two triality images
at `r`: either with the same signs or with both signs exchanged. Consequently, when both
images at `h` lie in an H-stable union of local orbits, so do both images at `r`. This is the
binary matching step for reverse bindings; it needs no central-sign computation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem singleton_square :
    inclQ singletonCocodeQ * inclQ singletonCocodeQ = (1 : H) := by
  rw [← map_mul]
  change inclQ (cocodeQ _ * cocodeQ _) = 1
  rw [cocodeQ_square, map_one]

private theorem sExtra_inv_eq_square (y : GriessSpace) : sExtra⁻¹ y = sExtra (sExtra y) := by
  apply sExtra.injective
  rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- The singleton cocode element also exchanges inverse triality with triality. -/
theorem generatedAxisGlobalTwelve_singleton_inverse_exchange (x : GriessSpace) :
    sExtra⁻¹ (rhoLocal (inclQ singletonCocodeQ) x) =
      rhoLocal (inclQ singletonCocodeQ) (sExtra x) := by
  have h := generatedAxisGlobal_singleton_triality_exchange (sExtra x)
  rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h
  rw [← h, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

/-- Inverse triality also normalizes the actual full Ω stabilizer on every vector. -/
theorem generatedAxisGlobalTwelve_omega_inverse_orbit (n : localOmegaStabilizer)
    (x : GriessSpace) :
    ∃ k : H, rhoLocal k (sExtra⁻¹ x) = sExtra⁻¹ (rhoLocal n.val x) := by
  obtain ⟨k1, hk1⟩ := localOmegaStabilizer_triality_conjugate n
  obtain ⟨k2, hk2⟩ := localOmegaStabilizer_triality_conjugate k1
  have e1 := congrArg Subtype.val hk1
  have e2 := congrArg Subtype.val hk2
  change sExtra * rhoLocal n.val * sExtra⁻¹ = rhoLocal k1.val at e1
  change sExtra * rhoLocal k1.val * sExtra⁻¹ = rhoLocal k2.val at e2
  have a1 (y : GriessSpace) : sExtra (rhoLocal n.val y) = rhoLocal k1.val (sExtra y) := by
    have he := LinearEquiv.congr_fun e1 (sExtra y)
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at he
    exact he
  have a2 (y : GriessSpace) : sExtra (rhoLocal k1.val y) = rhoLocal k2.val (sExtra y) := by
    have he := LinearEquiv.congr_fun e2 (sExtra y)
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at he
    exact he
  refine ⟨k2.val, ?_⟩
  rw [sExtra_inv_eq_square, sExtra_inv_eq_square, a1, a2]

/-- Both triality signs at `h` are local images of the two signs at `r`, as a pair. -/
theorem generatedAxisGlobalTwelve_root_relation_pair (v : GriessSpace) (h r c : H)
    (hfix : rhoLocal c v = v)
    (hroot : generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot r) =
      generatedAxisGlobalBinaryRoot h) :
    ((∃ k : H, sExtra (rhoLocal h v) = rhoLocal k (sExtra (rhoLocal r v))) ∧
      ∃ k : H, sExtra⁻¹ (rhoLocal h v) = rhoLocal k (sExtra⁻¹ (rhoLocal r v))) ∨
    ((∃ k : H, sExtra (rhoLocal h v) = rhoLocal k (sExtra⁻¹ (rhoLocal r v))) ∧
      ∃ k : H, sExtra⁻¹ (rhoLocal h v) = rhoLocal k (sExtra (rhoLocal r v))) := by
  have hone (x : generatedAxisGlobalBinaryOrbit) : generatedAxisGlobalBinaryAct 1 x = x := by
    apply Subtype.ext
    change co1BinaryAction (projH 1) x.val = x.val
    rw [map_one, map_one]
    rfl
  have ht := congrArg (generatedAxisGlobalBinaryAct h) hroot
  have hn : projH (h * c * r⁻¹) ∈ co1OmegaFrameStabilizer := by
    have ht' : generatedAxisGlobalBinaryAct (h * c * r⁻¹)
        generatedAxisGlobalBinaryOmega = generatedAxisGlobalBinaryOmega := by
      simpa only [generatedAxisGlobalBinaryRoot, ← generatedAxisGlobalBinaryAct_mul,
        mul_inv_cancel, hone, mul_assoc] using ht
    exact congrArg Subtype.val ht'
  have hfix' : rhoLocal c⁻¹ v = v := by
    have he := congrArg (rhoLocal c⁻¹) hfix
    simpa only [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, LinearEquiv.coe_one, id_eq] using he.symm
  rcases generatedAxisGlobal_binary_normalizer_split (h * c * r⁻¹) hn with h0 | h1
  · have hv : rhoLocal h v = rhoLocal (h * c * r⁻¹) (rhoLocal r v) := by
      have he : h = (h * c * r⁻¹) * r * c⁻¹ := by group
      conv_lhs => rw [he]
      rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix']
    left
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨h * c * r⁻¹, h0⟩ (rhoLocal r v)
      exact ⟨k, by rw [hv]; exact hk.symm⟩
    · obtain ⟨k, hk⟩ := generatedAxisGlobalTwelve_omega_inverse_orbit ⟨h * c * r⁻¹, h0⟩
        (rhoLocal r v)
      exact ⟨k, by rw [hv]; exact hk.symm⟩
  · have hv : rhoLocal h v = rhoLocal ((h * c * r⁻¹) * inclQ singletonCocodeQ)
        (rhoLocal (inclQ singletonCocodeQ) (rhoLocal r v)) := by
      have hel : (h * c * r⁻¹ * inclQ singletonCocodeQ) * inclQ singletonCocodeQ * r =
          h * c := by
        rw [mul_assoc (h * c * r⁻¹) (inclQ singletonCocodeQ) (inclQ singletonCocodeQ),
          singleton_square, mul_one, inv_mul_cancel_right]
      calc
        rhoLocal h v = rhoLocal (h * c) v := by rw [map_mul, LinearEquiv.mul_apply, hfix]
        _ = rhoLocal ((h * c * r⁻¹ * inclQ singletonCocodeQ) * inclQ singletonCocodeQ * r) v := by
          rw [hel]
        _ = _ := by rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    right
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit
        ⟨(h * c * r⁻¹) * inclQ singletonCocodeQ, h1⟩
        (rhoLocal (inclQ singletonCocodeQ) (rhoLocal r v))
      refine ⟨k * inclQ singletonCocodeQ, ?_⟩
      rw [hv, ← hk, generatedAxisGlobal_singleton_triality_exchange, map_mul,
        LinearEquiv.mul_apply]
    · obtain ⟨k, hk⟩ := generatedAxisGlobalTwelve_omega_inverse_orbit
        ⟨(h * c * r⁻¹) * inclQ singletonCocodeQ, h1⟩
        (rhoLocal (inclQ singletonCocodeQ) (rhoLocal r v))
      refine ⟨k * inclQ singletonCocodeQ, ?_⟩
      rw [hv, ← hk, generatedAxisGlobalTwelve_singleton_inverse_exchange, map_mul,
        LinearEquiv.mul_apply]

/-- A local image of a member of an actual local orbit union is again a member. -/
theorem generatedAxisGlobalTwelve_union_mem_of_local {ι : Type*} (u : ι → GriessSpace)
    {y z : GriessSpace} (k : H) (hy : y ∈ generatedLocalOrbitUnion u)
    (he : y = rhoLocal k z) : z ∈ generatedLocalOrbitUnion u := by
  have hz : z = rhoLocal k⁻¹ y := by
    rw [he, map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  rw [hz]
  exact generatedLocalOrbitUnion_local u k⁻¹ hy

/-- Both triality images at `h` in a local orbit union force both images at `r`. -/
theorem generatedAxisGlobalTwelve_root_pair_mem {ι : Type*} (u : ι → GriessSpace)
    (v : GriessSpace) (h r c : H) (hfix : rhoLocal c v = v)
    (hroot : generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot r) =
      generatedAxisGlobalBinaryRoot h)
    (hpos : sExtra (rhoLocal h v) ∈ generatedLocalOrbitUnion u)
    (hneg : sExtra⁻¹ (rhoLocal h v) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal r v) ∈ generatedLocalOrbitUnion u ∧
      sExtra⁻¹ (rhoLocal r v) ∈ generatedLocalOrbitUnion u := by
  rcases generatedAxisGlobalTwelve_root_relation_pair v h r c hfix hroot with
    ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ | ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩
  · exact ⟨generatedAxisGlobalTwelve_union_mem_of_local u k hpos hk,
      generatedAxisGlobalTwelve_union_mem_of_local u k' hneg hk'⟩
  · exact ⟨generatedAxisGlobalTwelve_union_mem_of_local u k' hneg hk',
      generatedAxisGlobalTwelve_union_mem_of_local u k hpos hk⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
