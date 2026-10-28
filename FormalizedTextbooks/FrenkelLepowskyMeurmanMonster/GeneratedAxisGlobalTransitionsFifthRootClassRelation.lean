/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary

/-! A single actual stabilizer orbit word suffices to compare two triality
transitions. The conclusion retains both genuine full-Ω signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem binaryActionIdentity (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalBinaryAct 1 x = x := by
  apply Subtype.ext
  change co1BinaryAction (projH 1) x.val = x.val
  rw [map_one, map_one]
  rfl

/-- An actual binary root transporter gives a full-vector local orbit relation,
with the two triality powers accounting for the lost central sign. -/
theorem generatedAxisGlobal_triality_root_relation (v : GriessSpace) (h r c : H)
    (hfix : rhoLocal c v = v)
    (hroot : generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot r) =
      generatedAxisGlobalBinaryRoot h) :
    (∃ k : H, sExtra (rhoLocal h v) = rhoLocal k (sExtra (rhoLocal r v))) ∨
      (∃ k : H, sExtra (rhoLocal h v) = rhoLocal k (sExtra⁻¹ (rhoLocal r v))) := by
  have ht := congrArg (generatedAxisGlobalBinaryAct h) hroot
  have hn : projH (h * c * r⁻¹) ∈ co1OmegaFrameStabilizer := by
    have ht' : generatedAxisGlobalBinaryAct (h * c * r⁻¹)
        generatedAxisGlobalBinaryOmega = generatedAxisGlobalBinaryOmega := by
      simpa only [generatedAxisGlobalBinaryRoot, ← generatedAxisGlobalBinaryAct_mul,
        mul_inv_cancel, binaryActionIdentity, mul_assoc] using ht
    exact congrArg Subtype.val ht'
  have hfix' : rhoLocal c⁻¹ v = v := by
    have he := congrArg (rhoLocal c⁻¹) hfix
    simpa only [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, LinearEquiv.coe_one, id_eq] using he.symm
  have he : h = (h * c * r⁻¹) * r * c⁻¹ := by group
  rcases generatedAxisGlobal_binary_normalizer_split (h * c * r⁻¹) hn with h0 | h1
  · left
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨h * c * r⁻¹, h0⟩
      (rhoLocal r v)
    refine ⟨k, ?_⟩
    rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix']
    exact hk.symm
  · right
    have hs : inclQ singletonCocodeQ * inclQ singletonCocodeQ = (1 : H) := by
      rw [← map_mul]
      change inclQ (cocodeQ _ * cocodeQ _) = 1
      rw [cocodeQ_square, map_one]
    have he' : h = ((h * c * r⁻¹) * inclQ singletonCocodeQ) *
        (inclQ singletonCocodeQ * r) * c⁻¹ := by
      calc
        h = (h * c * r⁻¹) * r * c⁻¹ := he
        _ = (h * c * r⁻¹) *
            (inclQ singletonCocodeQ * inclQ singletonCocodeQ) * r * c⁻¹ := by
          rw [hs, mul_one]
        _ = _ := by group
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit
      ⟨(h * c * r⁻¹) * inclQ singletonCocodeQ, h1⟩
      (rhoLocal (inclQ singletonCocodeQ * r) v)
    refine ⟨k * inclQ singletonCocodeQ, ?_⟩
    rw [he', map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix',
      ← hk, map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange,
      map_mul, LinearEquiv.mul_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
