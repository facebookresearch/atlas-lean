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
private theorem coefficient_column4 (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      4 = monsterNortonLine01TensorSeventhCoefficientLookup 4 p := by
  rw [monsterNortonLine01TensorSeventhCachedNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- A fixed physical row keeps the exact phase and sixteen-column numerator check bounded.
private theorem coefficient_column5 (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      5 = monsterNortonLine01TensorSeventhCoefficientLookup 5 p := by
  rw [monsterNortonLine01TensorSeventhCachedNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- A fixed physical row keeps the exact phase and sixteen-column numerator check bounded.
private theorem coefficient_column6 (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      6 = monsterNortonLine01TensorSeventhCoefficientLookup 6 p := by
  rw [monsterNortonLine01TensorSeventhCachedNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- A fixed physical row keeps the exact phase and sixteen-column numerator check bounded.
private theorem coefficient_column7 (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      7 = monsterNortonLine01TensorSeventhCoefficientLookup 7 p := by
  rw [monsterNortonLine01TensorSeventhCachedNumerator_actual]
  revert p
  decide +kernel

/-- Batch 1 of the exact actual seventh tensor coefficients. -/
theorem monsterNortonLine01TensorSeventh_coefficient_batch1 (i : Fin 4) (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      ⟨4 + i.val, by omega⟩ =
        monsterNortonLine01TensorSeventhCoefficientLookup ⟨4 + i.val, by omega⟩ p := by
  fin_cases i
  · exact coefficient_column4 p
  · exact coefficient_column5 p
  · exact coefficient_column6 p
  · exact coefficient_column7 p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
