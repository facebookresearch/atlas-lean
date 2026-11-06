/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthForestCertificate
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortInputs
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary

/-! Complete actual fifth-family transition reduction from the checked finite singular forest. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All actual binary Omega roots are covered by the fourteen original full local words. -/
theorem generatedAxisGlobalFifth_actual_binary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 14, ∃ c : H,
      c ∈ generatedFifthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthShortLocalWord i)) = x :=
  generatedAxisGlobalFifthShortLocalWord_cover_of_forest generatedAxisGlobalFifthForest_complete

/-- Every actual local element admits a phase-correct transition decomposition at these roots. -/
theorem generatedAxisGlobalFifth_actual_decompose (h : H) :
    ∃ i : Fin 14, ∃ n c : H, n ∈ localOmegaStabilizer ∧
      c ∈ generatedFifthLocalAxisStabilizer ∧
        (h = n * generatedAxisGlobalFifthShortLocalWord i * c ∨
          h = n * (inclQ singletonCocodeQ * generatedAxisGlobalFifthShortLocalWord i) * c) := by
  exact generatedAxisGlobal_decompose_two_signs generatedFifthLocalAxisStabilizer
    generatedAxisGlobalFifthShortLocalWord
    (generatedAxisGlobal_decompose_of_binary_cover generatedFifthLocalAxisStabilizer
      generatedAxisGlobalFifthShortLocalWord generatedAxisGlobalFifth_actual_binary_cover) h

/-- Twenty-eight full real vector transports suffice for all actual fifth-family transitions. -/
theorem generatedAxisGlobalFifth_triality_of_actual_destinations {ι : Type*}
    (v : ι → GriessSpace)
    (hpositive : ∀ i : Fin 14,
      sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ i : Fin 14,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis) ∈
        generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h generatedFifthAxis) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨i, n, c, hn, hc, he⟩ := generatedAxisGlobalFifth_actual_decompose h
  have hfix : rhoLocal c generatedFifthAxis = generatedFifthAxis := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord i) generatedFifthAxis)
    rw [← hk]
    exact generatedLocalOrbitUnion_local v k (hpositive i)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (inclQ singletonCocodeQ * generatedAxisGlobalFifthShortLocalWord i)
        generatedFifthAxis)
    rw [← hk]
    apply generatedLocalOrbitUnion_local v k
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
