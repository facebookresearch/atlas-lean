/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Bounded coefficient checks using proved fixed actual source input columns. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactStaticInputs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactColumnInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- The fixed actual column avoids retaining the larger variable-column coefficient tree.
private theorem coefficient_column8 (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector 8)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient 8 p := by
  rw [monsterNortonLine01CompactStaticInput8_actual,
    monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The fixed actual column avoids retaining the larger variable-column coefficient tree.
private theorem coefficient_column9 (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector 9)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient 9 p := by
  rw [monsterNortonLine01CompactStaticInput9_actual,
    monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The fixed actual column avoids retaining the larger variable-column coefficient tree.
private theorem coefficient_column10 (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector 10)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient 10 p := by
  rw [monsterNortonLine01CompactStaticInput10_actual,
    monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The fixed actual column avoids retaining the larger variable-column coefficient tree.
private theorem coefficient_column11 (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector 11)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient 11 p := by
  rw [monsterNortonLine01CompactStaticInput11_actual,
    monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

/-- Batch 2 of the full actual inverse numerator coefficient checks. -/
theorem monsterNortonLine01CompactInverse_coefficient_batch2 (k : Fin 4) (p : Fin 128) :
    monsterNortonUCompactInverseNumerator
      (monsterNortonLine01CompactInputVector ⟨8 + k.val, by omega⟩)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient ⟨8 + k.val, by omega⟩ p := by
  fin_cases k
  · exact coefficient_column8 p
  · exact coefficient_column9 p
  · exact coefficient_column10 p
  · exact coefficient_column11 p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
