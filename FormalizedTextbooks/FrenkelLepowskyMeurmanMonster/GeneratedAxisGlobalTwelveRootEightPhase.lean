/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightDecompose
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTrialityPhaseMerge
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightQRootFixed

/-! Seven of the 22 non-identity root-eight forest roots admit a genuine full-axis-fixing
extraspecial phase correction: the actual root operator `generatedFifthRootEightRootQ`, the
nonidentity extraspecial fixer of the whole root-eight axis, pairs oddly with the actual binary
root. Their two real triality transports need only one local class binding. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The seven root-eight roots whose Ω sign is flipped by the actual whole-axis Q fixer. -/
def rootEightForestMergedRoot : Fin 7 → Fin 23 :=
  ![1, 4, 5, 8, 9, 16, 19]

set_option maxRecDepth 100000 in
-- Evaluate the 24 coordinates of the whole-axis Q fixer.
/-- The binary class of the whole-axis Q fixer is the mask 6162432. -/
theorem rootEightForest_rootQ_mask :
    toAdd generatedFifthRootEightRootQ.base =
      monsterCo1GeometryBinaryMaskDecode (n := 24) 6162432 := by
  funext i
  revert i
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check seven complete 24-coordinate commutator pairings.
/-- The whole-axis Q fixer pairs oddly with the displayed mask of each merged root. -/
theorem rootEightForestMerged_pairing : ∀ j : Fin 7,
    qBeta (monsterCo1GeometryBinaryMaskDecode 6162432)
        (monsterCo1GeometryBinaryMaskDecode
          (rootEightForestRootMask (rootEightForestMergedRoot j))) +
      qBeta (monsterCo1GeometryBinaryMaskDecode
          (rootEightForestRootMask (rootEightForestMergedRoot j)))
        (monsterCo1GeometryBinaryMaskDecode 6162432) = 1 := by
  decide +kernel

/-- Both actual triality signs at the merged roots have the same full-vector local orbit. -/
theorem rootEightForestMerged_orbit (j : Fin 7) :
    ∃ k : H,
      sExtra (rhoLocal (rootEightForestRootWord (rootEightForestMergedRoot j))
        generatedFifthRootEightAxis) =
      rhoLocal k (sExtra⁻¹ (rhoLocal (rootEightForestRootWord (rootEightForestMergedRoot j))
        generatedFifthRootEightAxis)) := by
  apply generatedAxisGlobal_triality_phase_merge _ _ generatedFifthRootEightRootQ
    generatedFifthRootEight_root_Q_fixed
  rw [rootEightForest_rootQ_mask, rootEightForestRootWord_root]
  exact rootEightForestMerged_pairing j

/-- A positive local class binding at a merged root also binds its inverse image. -/
theorem rootEightForestMerged_negative_of_positive {ι : Type*} (v : ι → GriessSpace)
    (j : Fin 7)
    (hpositive : sExtra (rhoLocal (rootEightForestRootWord (rootEightForestMergedRoot j))
      generatedFifthRootEightAxis) ∈ generatedLocalOrbitUnion v) :
    sExtra⁻¹ (rhoLocal (rootEightForestRootWord (rootEightForestMergedRoot j))
      generatedFifthRootEightAxis) ∈ generatedLocalOrbitUnion v := by
  obtain ⟨k, hk⟩ := rootEightForestMerged_orbit j
  have he : sExtra⁻¹ (rhoLocal (rootEightForestRootWord (rootEightForestMergedRoot j))
      generatedFifthRootEightAxis) =
      rhoLocal k⁻¹ (sExtra (rhoLocal (rootEightForestRootWord (rootEightForestMergedRoot j))
        generatedFifthRootEightAxis)) := by
    rw [hk, map_inv]
    simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  rw [he]
  exact generatedLocalOrbitUnion_local v k⁻¹ hpositive

/-- A negative local class binding at a merged root also binds its forward image. -/
theorem rootEightForestMerged_positive_of_negative {ι : Type*} (v : ι → GriessSpace)
    (j : Fin 7)
    (hnegative : sExtra⁻¹ (rhoLocal (rootEightForestRootWord (rootEightForestMergedRoot j))
      generatedFifthRootEightAxis) ∈ generatedLocalOrbitUnion v) :
    sExtra (rhoLocal (rootEightForestRootWord (rootEightForestMergedRoot j))
      generatedFifthRootEightAxis) ∈ generatedLocalOrbitUnion v := by
  obtain ⟨k, hk⟩ := rootEightForestMerged_orbit j
  rw [hk]
  exact generatedLocalOrbitUnion_local v k hnegative

/-- The root indices that still need a negative binding: all but the identity coset and the
seven merged roots. -/
def rootEightForestNegativeOpen : Finset (Fin 23) :=
  {2, 3, 6, 7, 10, 11, 12, 13, 14, 15, 17, 18, 20, 21, 22}

set_option maxRecDepth 100000 in
-- Every root outside the open list is the identity coset or a merged root.
theorem rootEightForestNegativeOpen_complement :
    ∀ k : Fin 23, k ∉ rootEightForestNegativeOpen → k ≠ 0 →
      ∃ j : Fin 7, rootEightForestMergedRoot j = k := by
  decide +kernel

/-- Root-eight family coverage from the 22 forward triality images at the non-identity root
words and the 15 inverse images at the unmerged ones. -/
theorem generatedAxisGlobalTwelve_rootEight_covered_of_open
    (hpositive : ∀ k : Fin 23, k ≠ 0 →
      sExtra (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hnegative : ∀ k ∈ rootEightForestNegativeOpen,
      sExtra⁻¹ (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 9 := by
  apply generatedAxisGlobalTwelve_rootEight_covered_of hpositive
  intro k hk0
  by_cases hk : k ∈ rootEightForestNegativeOpen
  · exact hnegative k hk
  · obtain ⟨j, rfl⟩ := rootEightForestNegativeOpen_complement k hk hk0
    exact rootEightForestMerged_negative_of_positive _ j (hpositive _ hk0)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
