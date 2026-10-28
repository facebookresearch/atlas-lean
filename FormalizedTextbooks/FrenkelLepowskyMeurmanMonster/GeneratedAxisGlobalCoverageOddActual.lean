/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddForestCertificate
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceInputs
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary

/-! Complete actual odd-family transition reduction from the checked finite singular forest. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All actual binary Omega roots are covered by the nine original full local words. -/
theorem generatedAxisGlobalOdd_actual_binary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 9, ∃ c : H,
      c ∈ generatedOddLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalOddSourceRootLocalWord i)) = x :=
  generatedAxisGlobalOddSourceRootLocalWord_cover_of_forest generatedAxisGlobalOddForest_complete

/-- Every actual local element admits a phase-correct transition decomposition at these roots. -/
theorem generatedAxisGlobalOdd_actual_decompose (h : H) :
    ∃ i : Fin 9, ∃ n c : H, n ∈ localOmegaStabilizer ∧
      c ∈ generatedOddLocalAxisStabilizer ∧
        (h = n * generatedAxisGlobalOddSourceRootLocalWord i * c ∨
          h = n * (inclQ singletonCocodeQ * generatedAxisGlobalOddSourceRootLocalWord i) * c) := by
  exact generatedAxisGlobal_decompose_two_signs generatedOddLocalAxisStabilizer
    generatedAxisGlobalOddSourceRootLocalWord
    (generatedAxisGlobal_decompose_of_binary_cover generatedOddLocalAxisStabilizer
      generatedAxisGlobalOddSourceRootLocalWord generatedAxisGlobalOdd_actual_binary_cover) h

/-- Eighteen full real vector transports suffice for all actual odd-family transitions. -/
theorem generatedAxisGlobalOdd_triality_of_actual_destinations {ι : Type*}
    (v : ι → GriessSpace)
    (hpositive : ∀ i : Fin 9,
      sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord i) generatedOddAxis) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ i : Fin 9,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord i) generatedOddAxis) ∈
        generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h generatedOddAxis) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨i, n, c, hn, hc, he⟩ := generatedAxisGlobalOdd_actual_decompose h
  have hfix : rhoLocal c generatedOddAxis = generatedOddAxis := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord i) generatedOddAxis)
    rw [← hk]
    exact generatedLocalOrbitUnion_local v k (hpositive i)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (inclQ singletonCocodeQ * generatedAxisGlobalOddSourceRootLocalWord i)
        generatedOddAxis)
    rw [← hk]
    apply generatedLocalOrbitUnion_local v k
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
