/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthForestRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactCanonicalCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthFullQProjectionTransfer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelvePrototypeCosets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary

/-! The actual two-sign decomposition of every local element at the 65 Tenth root words, and the
reduction of the Tenth family coverage to the triality images at these words.

The only hypothesis is `GeneratedAxisGlobalTwelveTenthFixers`: the two genuine Tenth fibers fix
the whole canonical compact source axis. This is exactly the statement whose finite certificates
are still being gated (`generatedTenth_finite_certificates_two_fixers`). Under it, the six gated
Tenth letters are projections of whole-axis stabilizer elements of the listed Tenth axis, and the
checked bitset forest covers the whole binary Ω orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The two genuine Tenth fibers fix the whole canonical compact source axis. -/
def GeneratedAxisGlobalTwelveTenthFixers : Prop :=
  ∀ g : Fin 2, rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
    generatedTenthSourceCompactAxis = generatedTenthSourceCompactAxis

/-- The listed Tenth axis is a trivially projecting local image of the compact source axis. -/
theorem generatedAxisGlobalTwelveTenth_compact_transport :
    ∃ u : H, projH u = 1 ∧ generatedTenthAxis = rhoLocal u generatedTenthSourceCompactAxis := by
  obtain ⟨u, hu, he⟩ := generatedTwelfth_full_Q_triality_projection_orbit
    (generatedAxisGlobalFifthShortWordFiber 2) generatedTenthSourceCompactFiber
    generatedTenth_source_compact_fiber_full_Q generatedFifthAxis
  refine ⟨u, hu, ?_⟩
  rw [generatedAxisGlobalFifthShortWordFiber_local] at he
  rw [generatedTenthAxis_local_expression, generatedTenth_source_compact_axis_expression]
  exact he

/-- Under the two fixers, every gated Tenth letter is the projection of a whole-axis stabilizer
element of the listed Tenth axis. -/
theorem generatedAxisGlobalTwelveTenth_letter_mem (hfix : GeneratedAxisGlobalTwelveTenthFixers)
    (g : Fin 6) : generatedTenthAxisLowerRecoveryThreeProjectionLetter g ∈
      (MulAction.stabilizer H generatedTenthAxis).map projH := by
  have hcand (i : Fin 11) : generatedTenthAxisLowerRecoveryThreeProjectionActual i ∈
      generatedTenthSourceCompactCanonicalProjectedStabilizer :=
    generatedTenth_axis_lower_recovery_two_projection_candidates_mem
      generatedTenth_compact_spatial_binary_all
      generatedTenthSourceCompactCanonicalProjectedStabilizer
      (generatedTenth_source_compact_canonical_projected_mem hfix) i
  have hlet : generatedTenthAxisLowerRecoveryThreeProjectionLetter g ∈
      generatedTenthSourceCompactCanonicalProjectedStabilizer := by
    dsimp only [generatedTenthAxisLowerRecoveryThreeProjectionLetter]
    split_ifs
    · exact hcand _
    · exact Subgroup.inv_mem _ (hcand _)
  obtain ⟨c, hc⟩ := hlet
  obtain ⟨u, hu, he⟩ := generatedAxisGlobalTwelveTenth_compact_transport
  refine ⟨u * c.val * u⁻¹, ?_, ?_⟩
  · change rhoLocal (u * c.val * u⁻¹) generatedTenthAxis = generatedTenthAxis
    have hfixc : rhoLocal c.val generatedTenthSourceCompactAxis =
        generatedTenthSourceCompactAxis := c.property
    rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_inv,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, hfixc]
  · rw [map_mul, map_mul, hu, map_inv, hu, inv_one, one_mul, mul_one]
    exact hc

/-- Under the two fixers, every binary Ω point lies in the stabilizer orbit of a root word. -/
theorem generatedAxisGlobalTwelveTenth_actual_binary_cover
    (hfix : GeneratedAxisGlobalTwelveTenthFixers) :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ k : Fin 65, ∃ c : H,
      c ∈ MulAction.stabilizer H generatedTenthAxis ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveTenthRootWord k)) = x := by
  intro x
  obtain ⟨k, c, hc, he⟩ := generatedAxisGlobalTwelveTenth_binary_cover
    ((MulAction.stabilizer H generatedTenthAxis).map projH)
    (generatedAxisGlobalTwelveTenth_letter_mem hfix) x
  obtain ⟨c', hc', rfl⟩ := hc
  refine ⟨k, c', hc', ?_⟩
  apply Subtype.ext
  change co1BinaryAction (projH c')
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveTenthRootWord k)).val = x.val
  rw [generatedAxisGlobalTwelveTenthRootWord_root]
  exact he

/-- Under the two fixers, every local element decomposes phase-correctly at the root words. -/
theorem generatedAxisGlobalTwelveTenth_actual_decompose
    (hfix : GeneratedAxisGlobalTwelveTenthFixers) (h : H) :
    ∃ k : Fin 65, ∃ n c : H, n ∈ localOmegaStabilizer ∧
      c ∈ MulAction.stabilizer H generatedTenthAxis ∧
        (h = n * generatedAxisGlobalTwelveTenthRootWord k * c ∨
          h = n * (inclQ singletonCocodeQ * generatedAxisGlobalTwelveTenthRootWord k) * c) :=
  generatedAxisGlobal_decompose_two_signs (MulAction.stabilizer H generatedTenthAxis)
    generatedAxisGlobalTwelveTenthRootWord
    (generatedAxisGlobal_decompose_of_binary_cover (MulAction.stabilizer H generatedTenthAxis)
      generatedAxisGlobalTwelveTenthRootWord
      (generatedAxisGlobalTwelveTenth_actual_binary_cover hfix)) h

/-- Under the two fixers, the 130 triality images at the root words control the whole Tenth
family: if they lie in an actual local orbit union, so does every Tenth transition. -/
theorem generatedAxisGlobalTwelveTenth_triality_of_actual_destinations {ι : Type*}
    (v : ι → GriessSpace) (hfix : GeneratedAxisGlobalTwelveTenthFixers)
    (hpositive : ∀ k : Fin 65,
      sExtra (rhoLocal (generatedAxisGlobalTwelveTenthRootWord k) generatedTenthAxis) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ k : Fin 65,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveTenthRootWord k) generatedTenthAxis) ∈
        generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h generatedTenthAxis) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨k, n, c, hn, hc, he⟩ := generatedAxisGlobalTwelveTenth_actual_decompose hfix h
  have hfixc : rhoLocal c generatedTenthAxis = generatedTenthAxis := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfixc]
    obtain ⟨m, hm⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (generatedAxisGlobalTwelveTenthRootWord k) generatedTenthAxis)
    rw [← hm]
    exact generatedLocalOrbitUnion_local v m (hpositive k)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfixc]
    obtain ⟨m, hm⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (inclQ singletonCocodeQ * generatedAxisGlobalTwelveTenthRootWord k)
        generatedTenthAxis)
    rw [← hm]
    apply generatedLocalOrbitUnion_local v m
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative k)

/-- Both triality images at root word zero (the identity coset) lie in the twelve-family union:
forward to Tenth, inverse to Fifth. -/
theorem generatedAxisGlobalTwelveTenth_root_zero_pair :
    sExtra (rhoLocal (generatedAxisGlobalTwelveTenthRootWord 0)
        (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveTenthRootWord 0)
        (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [generatedAxisGlobalTwelveTenthRootWord_zero]
  exact generatedAxisGlobalTwelve_tenth_identity_pair

/-- Tenth family coverage from the two pending whole-axis fixers and the triality images at the
64 non-identity root words; root word zero is bound by the identity-coset pair. -/
theorem generatedAxisGlobalTwelve_tenth_covered_of (hfix : GeneratedAxisGlobalTwelveTenthFixers)
    (hpositive : ∀ k : Fin 65, k ≠ 0 →
      sExtra (rhoLocal (generatedAxisGlobalTwelveTenthRootWord k)
        (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hnegative : ∀ k : Fin 65, k ≠ 0 →
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveTenthRootWord k)
        (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 11 := by
  intro h
  apply generatedAxisGlobalTwelveTenth_triality_of_actual_destinations _ hfix
  · intro k
    by_cases hk : k = 0
    · subst hk; exact generatedAxisGlobalTwelveTenth_root_zero_pair.1
    · exact hpositive k hk
  · intro k
    by_cases hk : k = 0
    · subst hk; exact generatedAxisGlobalTwelveTenth_root_zero_pair.2
    · exact hnegative k hk

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
