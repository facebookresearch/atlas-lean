/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthForestCover
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthRootWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary

/-! Complete actual Sixth-family transition reduction from the checked finite singular forest.

Every local element factors through one of ten explicit root words, a genuine Ω-stabilizer
element and a genuine Sixth-axis stabilizer element, with one of two triality signs. Hence
twenty explicit vectors control all actual triality transitions of the Sixth family. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual binary Ω orbit is covered by the Sixth stabilizer images of the ten roots. -/
theorem generatedAxisGlobalTwelveSixth_actual_binary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 10, ∃ c : H,
      c ∈ generatedSixthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveSixthRootWord i)) = x := by
  intro x
  obtain ⟨i, c, hc, he⟩ := generatedAxisGlobalTwelveSixthBinary_cover
    generatedAxisGlobalTwelveSixthLongRoot_mem_orbit x
  refine ⟨i, c, hc, ?_⟩
  have hr : generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveSixthRootWord i) =
      ⟨_, generatedAxisGlobalTwelveSixthLongRoot_mem_orbit i⟩ :=
    Subtype.ext (generatedAxisGlobalTwelveSixthRootWord_root i)
  rw [hr]
  exact he

/-- Every actual local element admits a phase-correct transition decomposition at the ten
Sixth root words. -/
theorem generatedAxisGlobalTwelveSixth_actual_decompose (h : H) :
    ∃ i : Fin 10, ∃ n c : H, n ∈ localOmegaStabilizer ∧
      c ∈ generatedSixthLocalAxisStabilizer ∧
        (h = n * generatedAxisGlobalTwelveSixthRootWord i * c ∨
          h = n * (inclQ singletonCocodeQ * generatedAxisGlobalTwelveSixthRootWord i) * c) :=
  generatedAxisGlobal_decompose_two_signs generatedSixthLocalAxisStabilizer
    generatedAxisGlobalTwelveSixthRootWord
    (generatedAxisGlobal_decompose_of_binary_cover generatedSixthLocalAxisStabilizer
      generatedAxisGlobalTwelveSixthRootWord generatedAxisGlobalTwelveSixth_actual_binary_cover) h

/-- Twenty full real vector memberships suffice for all actual Sixth-family transitions. -/
theorem generatedAxisGlobalTwelveSixth_triality_of_actual_destinations {ι : Type*}
    (v : ι → GriessSpace)
    (hpositive : ∀ i : Fin 10,
      sExtra (rhoLocal (generatedAxisGlobalTwelveSixthRootWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ i : Fin 10,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveSixthRootWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h generatedSixthAxis) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨i, n, c, hn, hc, he⟩ := generatedAxisGlobalTwelveSixth_actual_decompose h
  have hfix : rhoLocal c generatedSixthAxis = generatedSixthAxis := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (generatedAxisGlobalTwelveSixthRootWord i) generatedSixthAxis)
    rw [← hk]
    exact generatedLocalOrbitUnion_local v k (hpositive i)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (inclQ singletonCocodeQ * generatedAxisGlobalTwelveSixthRootWord i)
        generatedSixthAxis)
    rw [← hk]
    apply generatedLocalOrbitUnion_local v k
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
