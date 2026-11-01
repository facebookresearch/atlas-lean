/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual inverse triality on physical pair units and pure diagonal matrices. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityProduct

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Inverse extra maps each whole pair short unit to its exact B,A dictionary combination. -/
theorem monsterNortonPairShort_extra_inverse (s : Fin 2) (p : Fin 276) :
    sExtra.symm (monsterNortonPureShort (Sum.inl (s, p))) =
      (1 / 2 : ℝ) • trialityABCBasis 1 p +
        (if s = 0 then (1 / 2 : ℝ) else -1 / 2) • trialityABCBasis 0 p := by
  apply sExtra.injective
  rw [LinearEquiv.apply_symm_apply, map_add, map_smul, map_smul,
    sExtra_ABC_basis, sExtra_ABC_basis, monsterNortonPairShort_ABC]
  rfl

/-- The entire pure diagonal matrix is fixed by actual inverse triality. -/
theorem monsterNortonDiagonal_extra_inverse (d : Fin 24 → ℝ) :
    sExtra.symm (griessConwayDecode (Matrix.diagonal d, (0, 0))) =
      griessConwayDecode (Matrix.diagonal d, (0, 0)) := by
  have hd : griessConwayDecode (Matrix.diagonal d, (0, 0)) = trialityDiagonalVector d := by
    rw [← griessConwayEncode_diagonal, griessConwayDecode_encode]
  rw [hd]
  apply sExtra.injective
  rw [LinearEquiv.apply_symm_apply, sExtra_diagonal]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
