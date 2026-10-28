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
private theorem coefficient_column12 (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      12 = monsterNortonLine01TensorSeventhCoefficientLookup 12 p := by
  rw [monsterNortonLine01TensorSeventhCachedNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- A fixed physical row keeps the exact phase and sixteen-column numerator check bounded.
private theorem coefficient_column13 (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      13 = monsterNortonLine01TensorSeventhCoefficientLookup 13 p := by
  rw [monsterNortonLine01TensorSeventhCachedNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- A fixed physical row keeps the exact phase and sixteen-column numerator check bounded.
private theorem coefficient_column14 (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      14 = monsterNortonLine01TensorSeventhCoefficientLookup 14 p := by
  rw [monsterNortonLine01TensorSeventhCachedNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- A fixed physical row keeps the exact phase and sixteen-column numerator check bounded.
private theorem coefficient_column15 (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      15 = monsterNortonLine01TensorSeventhCoefficientLookup 15 p := by
  rw [monsterNortonLine01TensorSeventhCachedNumerator_actual]
  revert p
  decide +kernel

/-- Batch 3 of the exact actual seventh tensor coefficients. -/
theorem monsterNortonLine01TensorSeventh_coefficient_batch3 (i : Fin 4) (p : Fin 128) :
    monsterNortonLine01TensorSeventhIntegerNumerator (monsterNortonLine01TensorSpinLabel p)
      ⟨12 + i.val, by omega⟩ =
        monsterNortonLine01TensorSeventhCoefficientLookup ⟨12 + i.val, by omega⟩ p := by
  fin_cases i
  · exact coefficient_column12 p
  · exact coefficient_column13 p
  · exact coefficient_column14 p
  · exact coefficient_column15 p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
