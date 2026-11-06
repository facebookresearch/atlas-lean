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
private theorem coefficient_column12 (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector 12)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient 12 p := by
  rw [monsterNortonLine01CompactStaticInput12_actual,
    monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The fixed actual column avoids retaining the larger variable-column coefficient tree.
private theorem coefficient_column13 (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector 13)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient 13 p := by
  rw [monsterNortonLine01CompactStaticInput13_actual,
    monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The fixed actual column avoids retaining the larger variable-column coefficient tree.
private theorem coefficient_column14 (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector 14)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient 14 p := by
  rw [monsterNortonLine01CompactStaticInput14_actual,
    monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The fixed actual column avoids retaining the larger variable-column coefficient tree.
private theorem coefficient_column15 (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector 15)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient 15 p := by
  rw [monsterNortonLine01CompactStaticInput15_actual,
    monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

/-- Batch 3 of the full actual inverse numerator coefficient checks. -/
theorem monsterNortonLine01CompactInverse_coefficient_batch3 (k : Fin 4) (p : Fin 128) :
    monsterNortonUCompactInverseNumerator
      (monsterNortonLine01CompactInputVector ⟨12 + k.val, by omega⟩)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient ⟨12 + k.val, by omega⟩ p := by
  fin_cases k
  · exact coefficient_column12 p
  · exact coefficient_column13 p
  · exact coefficient_column14 p
  · exact coefficient_column15 p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
