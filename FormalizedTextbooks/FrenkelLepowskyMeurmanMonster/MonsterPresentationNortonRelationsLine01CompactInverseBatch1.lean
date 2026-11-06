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
private theorem coefficient_column4 (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector 4)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient 4 p := by
  rw [monsterNortonLine01CompactStaticInput4_actual,
    monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The fixed actual column avoids retaining the larger variable-column coefficient tree.
private theorem coefficient_column5 (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector 5)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient 5 p := by
  rw [monsterNortonLine01CompactStaticInput5_actual,
    monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The fixed actual column avoids retaining the larger variable-column coefficient tree.
private theorem coefficient_column6 (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector 6)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient 6 p := by
  rw [monsterNortonLine01CompactStaticInput6_actual,
    monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The fixed actual column avoids retaining the larger variable-column coefficient tree.
private theorem coefficient_column7 (p : Fin 128) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector 7)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient 7 p := by
  rw [monsterNortonLine01CompactStaticInput7_actual,
    monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

/-- Batch 1 of the full actual inverse numerator coefficient checks. -/
theorem monsterNortonLine01CompactInverse_coefficient_batch1 (k : Fin 4) (p : Fin 128) :
    monsterNortonUCompactInverseNumerator
      (monsterNortonLine01CompactInputVector ⟨4 + k.val, by omega⟩)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient ⟨4 + k.val, by omega⟩ p := by
  fin_cases k
  · exact coefficient_column4 p
  · exact coefficient_column5 p
  · exact coefficient_column6 p
  · exact coefficient_column7 p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
