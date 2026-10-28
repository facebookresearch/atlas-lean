/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightForestRoots
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightSpatial
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightActualLocalCount
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverMateActualFixers
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelvePrototypeCosets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary

/-! The actual two-sign decomposition of every local element at the 23 root-eight root words,
and the reduction of the root-eight family coverage to the triality images at these words.

The four root-eight letters are projections of genuine whole-axis fixers of the listed
root-eight axis: each is the canonical-transport conjugate of an original canonical generator
(two reduced Mathieu words, the point mover, the mate orientation) that is attained by an
actual fixer of the canonical positive axis. The checked bitset forest then covers the whole
binary Ω orbit, with no further hypothesis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every root-eight forest letter is the projection of a genuine whole-axis fixer of the
listed root-eight axis. -/
theorem rootEightForest_letter_mem (k : Fin 4) :
    QuotientGroup.mk' signsSubgroup (rootEightForestIsometry k) ∈
      generatedFifthRootEightProjectedAxisStabilizer := by
  rw [rootEightForestIsometry, ← generatedRootEight_canonical_quotient_conjugation]
  apply generatedRootEight_original_projection_of_canonical_fixer
  fin_cases k
  · exact generatedRootEight_mathieu_actual_fixer_projection 0
  · exact generatedRootEight_mathieu_actual_fixer_projection 1
  · exact generatedRootEight_mover_actual_fixer_projection
  · exact generatedRootEight_mate_actual_fixer_projection

/-- The same membership, in the form of an image of the whole-axis stabilizer. -/
theorem rootEightForest_letter_mem_map (k : Fin 4) :
    QuotientGroup.mk' signsSubgroup (rootEightForestIsometry k) ∈
      (MulAction.stabilizer H generatedFifthRootEightAxis).map projH := by
  obtain ⟨c, hc⟩ := rootEightForest_letter_mem k
  exact ⟨c.val, c.property, hc⟩

/-- The genuine letters act on Λ/2Λ exactly by the forest columns. -/
theorem rootEightForest_lifts :
    RootEightForestLifts (fun k => QuotientGroup.mk' signsSubgroup (rootEightForestIsometry k)) :=
  rootEightForestIsometry_binary

/-- Every binary Ω point lies in the whole-axis stabilizer orbit of a root word. -/
theorem generatedAxisGlobalTwelveRootEight_actual_binary_cover :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ k : Fin 23, ∃ c : H,
      c ∈ MulAction.stabilizer H generatedFifthRootEightAxis ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (rootEightForestRootWord k)) = x := by
  intro x
  obtain ⟨k, c, hc, he⟩ := rootEightForest_binary_cover rootEightForest_lifts
    ((MulAction.stabilizer H generatedFifthRootEightAxis).map projH)
    rootEightForest_letter_mem_map x
  obtain ⟨c', hc', rfl⟩ := hc
  refine ⟨k, c', hc', ?_⟩
  apply Subtype.ext
  change co1BinaryAction (projH c')
    (generatedAxisGlobalBinaryRoot (rootEightForestRootWord k)).val = x.val
  rw [rootEightForestRootWord_root]
  exact he

/-- Every local element decomposes phase-correctly at the root-eight root words. -/
theorem generatedAxisGlobalTwelveRootEight_actual_decompose (h : H) :
    ∃ k : Fin 23, ∃ n c : H, n ∈ localOmegaStabilizer ∧
      c ∈ MulAction.stabilizer H generatedFifthRootEightAxis ∧
        (h = n * rootEightForestRootWord k * c ∨
          h = n * (inclQ singletonCocodeQ * rootEightForestRootWord k) * c) :=
  generatedAxisGlobal_decompose_two_signs (MulAction.stabilizer H generatedFifthRootEightAxis)
    rootEightForestRootWord
    (generatedAxisGlobal_decompose_of_binary_cover
      (MulAction.stabilizer H generatedFifthRootEightAxis) rootEightForestRootWord
      generatedAxisGlobalTwelveRootEight_actual_binary_cover) h

/-- The 46 triality images at the root words control the whole root-eight family: if they lie
in an actual local orbit union, so does every root-eight transition. -/
theorem generatedAxisGlobalTwelveRootEight_triality_of_actual_destinations {ι : Type*}
    (v : ι → GriessSpace)
    (hpositive : ∀ k : Fin 23,
      sExtra (rhoLocal (rootEightForestRootWord k) generatedFifthRootEightAxis) ∈
        generatedLocalOrbitUnion v)
    (hnegative : ∀ k : Fin 23,
      sExtra⁻¹ (rhoLocal (rootEightForestRootWord k) generatedFifthRootEightAxis) ∈
        generatedLocalOrbitUnion v) :
    ∀ h : H, sExtra (rhoLocal h generatedFifthRootEightAxis) ∈ generatedLocalOrbitUnion v := by
  intro h
  obtain ⟨k, n, c, hn, hc, he⟩ := generatedAxisGlobalTwelveRootEight_actual_decompose h
  have hfixc : rhoLocal c generatedFifthRootEightAxis = generatedFifthRootEightAxis := hc
  rcases he with he | he
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfixc]
    obtain ⟨m, hm⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (rootEightForestRootWord k) generatedFifthRootEightAxis)
    rw [← hm]
    exact generatedLocalOrbitUnion_local v m (hpositive k)
  · rw [he, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfixc]
    obtain ⟨m, hm⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩
      (rhoLocal (inclQ singletonCocodeQ * rootEightForestRootWord k)
        generatedFifthRootEightAxis)
    rw [← hm]
    apply generatedLocalOrbitUnion_local v m
    rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange]
    exact generatedLocalOrbitUnion_local v (inclQ singletonCocodeQ) (hnegative k)

/-- Both triality images at root word zero (the identity coset) lie in the twelve-family union:
forward to the root-eight family, inverse to the Fifth family. -/
theorem generatedAxisGlobalTwelveRootEight_root_zero_pair :
    sExtra (rhoLocal (rootEightForestRootWord 0)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (rootEightForestRootWord 0)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [rootEightForestRootWord_zero]
  exact generatedAxisGlobalTwelve_root8_identity_pair

/-- Root-eight family coverage from the triality images at the 22 non-identity root words;
root word zero is bound by the identity-coset pair. -/
theorem generatedAxisGlobalTwelve_rootEight_covered_of
    (hpositive : ∀ k : Fin 23, k ≠ 0 →
      sExtra (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hnegative : ∀ k : Fin 23, k ≠ 0 →
      sExtra⁻¹ (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 9 := by
  intro h
  apply generatedAxisGlobalTwelveRootEight_triality_of_actual_destinations
  · intro k
    by_cases hk : k = 0
    · subst hk
      exact generatedAxisGlobalTwelveRootEight_root_zero_pair.1
    · exact hpositive k hk
  · intro k
    by_cases hk : k = 0
    · subst hk
      exact generatedAxisGlobalTwelveRootEight_root_zero_pair.2
    · exact hnegative k hk

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
