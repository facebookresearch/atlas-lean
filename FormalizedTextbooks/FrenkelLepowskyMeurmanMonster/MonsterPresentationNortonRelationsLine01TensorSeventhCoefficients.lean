/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact assembly of all supported tensor coefficients after seven actual word steps. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSeventhCoefficientBatch0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSeventhCoefficientBatch1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSeventhCoefficientBatch2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSeventhCoefficientBatch3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SpinSupport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every supported seventh tensor numerator is the kernel-checked integer table entry. -/
theorem monsterNortonLine01TensorSeventh_coefficients (i : Fin 16) (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      (Fin.castLE (by omega) i) = monsterNortonLine01TensorSeventhCoefficientLookup i p := by
  fin_cases i
  · exact monsterNortonLine01TensorSeventh_coefficient_batch0 0 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch0 1 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch0 2 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch0 3 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch1 0 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch1 1 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch1 2 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch1 3 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch2 0 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch2 1 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch2 2 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch2 3 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch3 0 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch3 1 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch3 2 p
  · exact monsterNortonLine01TensorSeventh_coefficient_batch3 3 p

/-- The supported entries of the entire actual seventh tensor state have their exact real scale. -/
theorem monsterNortonLine01TensorSeventh_coefficients_actual (i : Fin 16) (p : Fin 128) :
    (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.2
      (golayLabelCoefficients (monsterNortonLine01TensorSpinLabel p))
        (Fin.castLE (by omega) i) =
          (1 / (4096 * Real.sqrt 2) : ℝ) *
            (monsterNortonLine01TensorSeventhCoefficientLookup i p : ℝ) := by
  rw [monsterNortonLine01TensorSeventhInteger_actual,
    monsterNortonLine01TensorSeventh_coefficients]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
