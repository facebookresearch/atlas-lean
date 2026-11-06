/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhForestCover
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhRootWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary

/-! Complete actual Seventh-family transition reduction from the checked finite singular forest.

Every local element factors through one of 23 explicit root words, a genuine Ω-stabilizer
element and a genuine Seventh-axis stabilizer element, with one of two triality signs. Hence
46 explicit vectors control all actual triality transitions of the Seventh family. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual binary Ω orbit is covered by the Seventh stabilizer images of the 23 roots. -/
theorem generatedAxisGlobalTwelveSeventh_actual_binary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 23, ∃ c : H,
      c ∈ generatedSeventhLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveSeventhRootWord i)) = x := by
  intro x
  obtain ⟨i, c, hc, he⟩ := generatedAxisGlobalTwelveSeventhBinary_cover
    generatedAxisGlobalTwelveSeventhLongRoot_mem_orbit x
  refine ⟨i, c, hc, ?_⟩
  have hr : generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveSeventhRootWord i) =
      ⟨_, generatedAxisGlobalTwelveSeventhLongRoot_mem_orbit i⟩ :=
    Subtype.ext (generatedAxisGlobalTwelveSeventhRootWord_root i)
  rw [hr]
  exact he

/-- Every actual local element admits a phase-correct transition decomposition at the 23
Seventh root words. -/
theorem generatedAxisGlobalTwelveSeventh_actual_decompose (h : H) :
    ∃ i : Fin 23, ∃ n c : H, n ∈ localOmegaStabilizer ∧
      c ∈ generatedSeventhLocalAxisStabilizer ∧
        (h = n * generatedAxisGlobalTwelveSeventhRootWord i * c ∨
          h = n * (inclQ singletonCocodeQ * generatedAxisGlobalTwelveSeventhRootWord i) * c) :=
  generatedAxisGlobal_decompose_two_signs generatedSeventhLocalAxisStabilizer
    generatedAxisGlobalTwelveSeventhRootWord
    (generatedAxisGlobal_decompose_of_binary_cover generatedSeventhLocalAxisStabilizer
      generatedAxisGlobalTwelveSeventhRootWord
      generatedAxisGlobalTwelveSeventh_actual_binary_cover) h

/-- Forty-six full real vector memberships suffice for all actual Seventh-family transitions. -/
theorem generatedAxisGlobalTwelveSeventh_triality_of_actual_destinations {ι : Type*}
    (v : ι → GriessSpace)
    (hpositive : ∀ i : Fin 23,
      sExtra (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ i : Fin 23,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h generatedSeventhAxis) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨i, n, c, hn, hc, he⟩ := generatedAxisGlobalTwelveSeventh_actual_decompose h
  have hfix : rhoLocal c generatedSeventhAxis = generatedSeventhAxis := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord i) generatedSeventhAxis)
    rw [← hk]
    exact generatedLocalOrbitUnion_local v k (hpositive i)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfix]
    obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (inclQ singletonCocodeQ * generatedAxisGlobalTwelveSeventhRootWord i)
        generatedSeventhAxis)
    rw [← hk]
    apply generatedLocalOrbitUnion_local v k
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
