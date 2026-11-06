/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthForestRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTrialityPhaseMerge
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthQStabilizerExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineParameterBasisData

/-! Eleven of the sixteen Fourth forest roots admit a genuine full-axis-fixing extraspecial
phase correction: one of the seven actual generators of the Fourth-axis Q stabilizer pairs oddly
with the actual binary root. Their two real triality transports need only one local class
binding. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The eleven Fourth roots whose Ω sign is flipped by an actual full-axis Q fixer. -/
def generatedAxisGlobalTwelveFourthMergedRoot : Fin 11 → Fin 16 :=
  ![0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13]

/-- For each merged root, an actual Fourth-axis Q-stabilizer generator pairing oddly with it. -/
def generatedAxisGlobalTwelveFourthMergedFixer : Fin 11 → Fin 7 :=
  ![2, 2, 2, 1, 3, 1, 2, 1, 1, 1, 2]

set_option maxHeartbeats 4000000 in
-- Check eleven complete 24-coordinate commutator pairings.
/-- Each listed generator pairs oddly with the displayed mask of its merged root. -/
theorem generatedAxisGlobalTwelveFourthMerged_pairing : ∀ j : Fin 11,
    qBeta (toAdd (generatedFourthQAffineParameterBasis
          (generatedAxisGlobalTwelveFourthMergedFixer j)).base)
        (monsterCo1GeometryBinaryMaskDecode
          (generatedAxisGlobalTwelveFourthRootMask (generatedAxisGlobalTwelveFourthMergedRoot j))) +
      qBeta (monsterCo1GeometryBinaryMaskDecode
          (generatedAxisGlobalTwelveFourthRootMask (generatedAxisGlobalTwelveFourthMergedRoot j)))
        (toAdd (generatedFourthQAffineParameterBasis
          (generatedAxisGlobalTwelveFourthMergedFixer j)).base) = 1 := by
  simp only [generatedFourthQAffineParameterBasis_literal]
  decide +kernel

/-- Both actual triality signs at the merged roots have the same full-vector local orbit. -/
theorem generatedAxisGlobalTwelveFourthMerged_orbit (j : Fin 11) :
    ∃ k : H,
      sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
        (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis) =
      rhoLocal k (sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
        (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis)) := by
  apply generatedAxisGlobal_triality_phase_merge _ _
    (generatedFourthQAffineParameterBasis (generatedAxisGlobalTwelveFourthMergedFixer j))
  · exact generatedFourth_axis_q_basis_mem (generatedAxisGlobalTwelveFourthMergedFixer j)
  · change qBeta _ (generatedAxisGlobalTwelveFourthRoot
        (generatedAxisGlobalTwelveFourthMergedRoot j)).val +
      qBeta (generatedAxisGlobalTwelveFourthRoot
        (generatedAxisGlobalTwelveFourthMergedRoot j)).val _ = 1
    rw [generatedAxisGlobalTwelveFourthRoot_val]
    exact generatedAxisGlobalTwelveFourthMerged_pairing j

/-- A positive local class binding at a merged root also binds its inverse image. -/
theorem generatedAxisGlobalTwelveFourthMerged_negative_of_positive {ι : Type*}
    (v : ι → GriessSpace) (j : Fin 11)
    (hpositive : sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
      (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion v) :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
      (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion v := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalTwelveFourthMerged_orbit j
  have he : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
      (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis) =
      rhoLocal k⁻¹ (sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
        (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis)) := by
    rw [hk, map_inv]
    simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  rw [he]
  exact generatedLocalOrbitUnion_local v k⁻¹ hpositive

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
