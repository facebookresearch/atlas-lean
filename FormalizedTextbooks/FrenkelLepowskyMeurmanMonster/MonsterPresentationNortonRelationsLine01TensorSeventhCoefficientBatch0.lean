/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Bounded actual seventh tensor coefficient checks for four fixed physical rows. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSeventhCoefficientData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- A fixed physical row keeps the exact phase and sixteen-column numerator check bounded.
private theorem coefficient_column0 (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      0 = monsterNortonLine01TensorSeventhCoefficientLookup 0 p := by
  rw [monsterNortonLine01TensorSeventhCachedNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- A fixed physical row keeps the exact phase and sixteen-column numerator check bounded.
private theorem coefficient_column1 (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      1 = monsterNortonLine01TensorSeventhCoefficientLookup 1 p := by
  rw [monsterNortonLine01TensorSeventhCachedNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- A fixed physical row keeps the exact phase and sixteen-column numerator check bounded.
private theorem coefficient_column2 (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      2 = monsterNortonLine01TensorSeventhCoefficientLookup 2 p := by
  rw [monsterNortonLine01TensorSeventhCachedNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- A fixed physical row keeps the exact phase and sixteen-column numerator check bounded.
private theorem coefficient_column3 (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      3 = monsterNortonLine01TensorSeventhCoefficientLookup 3 p := by
  rw [monsterNortonLine01TensorSeventhCachedNumerator_actual]
  revert p
  decide +kernel

/-- Batch 0 of the exact actual seventh tensor coefficients. -/
theorem monsterNortonLine01TensorSeventh_coefficient_batch0 (i : Fin 4) (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      ⟨0 + i.val, by omega⟩ =
        monsterNortonLine01TensorSeventhCoefficientLookup ⟨0 + i.val, by omega⟩ p := by
  fin_cases i
  · exact coefficient_column0 p
  · exact coefficient_column1 p
  · exact coefficient_column2 p
  · exact coefficient_column3 p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
