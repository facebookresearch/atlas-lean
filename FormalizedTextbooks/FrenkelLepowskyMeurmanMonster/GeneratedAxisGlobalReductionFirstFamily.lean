/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionPairMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageFirstLayer

/-! A complete actual three-root transition decomposition for the first local
axis orbit. The proof uses genuine monomial transports on every short label;
it does not assume any finite orbit table or global Monster order. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Three actual short labels representing the three monomial families. -/
def generatedAxisGlobalFirstInputIndex : Fin 3 → GriessShortIndex :=
  ![Sum.inl (0, 0), Sum.inr (Sum.inl (0, 0)), Sum.inr (Sum.inr (0, 0))]

/-- Each actual short-family representative is attained by an actual local element. -/
theorem generatedAxisGlobalFirstInput_attained (i : Fin 3) :
    ∃ h : H, rhoLocal h (conwayAxis 0) =
      conwayShortAxis (generatedAxisGlobalFirstInputIndex i) 0 := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive (Sum.inl (0, 0))
    (generatedAxisGlobalFirstInputIndex i) 0 0
  rw [conwayShortAxis_pair_zero] at hh
  exact ⟨h, hh⟩

/-- Three genuine local transition representatives, with their full spin phases. -/
noncomputable def generatedAxisGlobalFirstInputLocal (i : Fin 3) : H :=
  Classical.choose (generatedAxisGlobalFirstInput_attained i)

/-- The actual action of each chosen transition representative. -/
theorem generatedAxisGlobalFirstInputLocal_apply (i : Fin 3) :
    rhoLocal (generatedAxisGlobalFirstInputLocal i) (conwayAxis 0) =
      conwayShortAxis (generatedAxisGlobalFirstInputIndex i) 0 :=
  Classical.choose_spec (generatedAxisGlobalFirstInput_attained i)

/-- All actual signed-short axes are covered by three Ω-centralizer orbits. -/
theorem generatedAxisGlobalFirstInput_omega_cover (r : GriessShortIndex) (c : ZMod 2) :
    ∃ i : Fin 3, ∃ n : localOmegaStabilizer,
      rhoLocal n.val (conwayShortAxis (generatedAxisGlobalFirstInputIndex i) 0) =
        conwayShortAxis r c := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · obtain ⟨a, ha, hl⟩ := generatedAxisGlobal_pair_monomial_transitive 0 s 0 p
    obtain ⟨n, hn⟩ := generatedAxis_monomial_signed_localOmega _ _ a ha hl 0 c
    exact ⟨0, n, hn⟩
  · obtain ⟨a, ha, hl⟩ := generatedAxis_octad_monomial_transitive 0 o 0 e
    obtain ⟨n, hn⟩ := generatedAxis_monomial_signed_localOmega _ _ a ha hl 0 c
    exact ⟨1, n, hn⟩
  · obtain ⟨a, ha, hl⟩ := generatedAxis_odd_monomial_transitive 0 d 0 j
    obtain ⟨n, hn⟩ := generatedAxis_monomial_signed_localOmega _ _ a ha hl 0 c
    exact ⟨2, n, hn⟩

/-- Every actual local transition input has a genuine three-root N--C
factorization, with C the actual first-axis stabilizer. -/
theorem generatedAxisGlobalFirstFamily_decompose (h : H) :
    ∃ i : Fin 3, ∃ n : localOmegaStabilizer, ∃ c : localAxisStabilizer 0,
      h = n.val * generatedAxisGlobalFirstInputLocal i * c.val := by
  have hs : rhoLocal h (conwayAxis 0) ∈ generatedSignedShortAxes := by
    rw [← generatedAxisLocalActual_orbit_eq_signed 0]
    exact ⟨h, rfl⟩
  obtain ⟨⟨r, d⟩, hx⟩ := hs
  obtain ⟨i, n, hn⟩ := generatedAxisGlobalFirstInput_omega_cover r d
  let a := n.val * generatedAxisGlobalFirstInputLocal i
  have ha : rhoLocal a (conwayAxis 0) = rhoLocal h (conwayAxis 0) := by
    change rhoLocal (n.val * generatedAxisGlobalFirstInputLocal i) (conwayAxis 0) = _
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobalFirstInputLocal_apply, hn]
    exact hx
  have hc : a⁻¹ * h ∈ localAxisStabilizer 0 := by
    change rhoLocal (a⁻¹ * h) (conwayAxis 0) = conwayAxis 0
    rw [map_mul, LinearEquiv.mul_apply, ← ha, map_inv]
    exact LinearEquiv.symm_apply_apply _ _
  refine ⟨i, n, ⟨a⁻¹ * h, hc⟩, ?_⟩
  change h = n.val * generatedAxisGlobalFirstInputLocal i * (a⁻¹ * h)
  change h = a * (a⁻¹ * h)
  rw [mul_inv_cancel_left]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
