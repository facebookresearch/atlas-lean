/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual odd-short coordinate simplification at the eleventh word step. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhOddCoefficientBatch0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhOddCoefficientBatch1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhOddCoefficientBatch2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhOddCoefficientBatch3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhOddSupport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All source-code coordinates have the exact singleton eleventh odd-short numerator. -/
theorem monsterNortonLine01EleventhOdd_source_coefficients (a : Fin 64) (i : Fin 24) :
    monsterNortonLine01EleventhOddIntegerNumerator (monsterNortonLine01ShortInputCode a) i =
      if monsterNortonLine01ShortInputCode a = 82 ∧ i.val = 1 then 256 else 0 := by
  fin_cases i
  · exact monsterNortonLine01EleventhOdd_coefficient_batch0 a 0
  · exact monsterNortonLine01EleventhOdd_coefficient_batch0 a 1
  · exact monsterNortonLine01EleventhOdd_coefficient_batch0 a 2
  · exact monsterNortonLine01EleventhOdd_coefficient_batch0 a 3
  · exact monsterNortonLine01EleventhOdd_coefficient_batch0 a 4
  · exact monsterNortonLine01EleventhOdd_coefficient_batch0 a 5
  · exact monsterNortonLine01EleventhOdd_coefficient_batch1 a 0
  · exact monsterNortonLine01EleventhOdd_coefficient_batch1 a 1
  · exact monsterNortonLine01EleventhOdd_coefficient_batch1 a 2
  · exact monsterNortonLine01EleventhOdd_coefficient_batch1 a 3
  · exact monsterNortonLine01EleventhOdd_coefficient_batch1 a 4
  · exact monsterNortonLine01EleventhOdd_coefficient_batch1 a 5
  · exact monsterNortonLine01EleventhOdd_coefficient_batch2 a 0
  · exact monsterNortonLine01EleventhOdd_coefficient_batch2 a 1
  · exact monsterNortonLine01EleventhOdd_coefficient_batch2 a 2
  · exact monsterNortonLine01EleventhOdd_coefficient_batch2 a 3
  · exact monsterNortonLine01EleventhOdd_coefficient_batch2 a 4
  · exact monsterNortonLine01EleventhOdd_coefficient_batch2 a 5
  · exact monsterNortonLine01EleventhOdd_coefficient_batch3 a 0
  · exact monsterNortonLine01EleventhOdd_coefficient_batch3 a 1
  · exact monsterNortonLine01EleventhOdd_coefficient_batch3 a 2
  · exact monsterNortonLine01EleventhOdd_coefficient_batch3 a 3
  · exact monsterNortonLine01EleventhOdd_coefficient_batch3 a 4
  · exact monsterNortonLine01EleventhOdd_coefficient_batch3 a 5

/-- The entire eleventh odd-short numerator is a singleton, including unsupported source codes. -/
theorem monsterNortonLine01EleventhOddInteger_singleton (d : Fin 2048) (i : Fin 24) :
    monsterNortonLine01EleventhOddIntegerNumerator d i =
      if d = 82 ∧ i.val = 1 then 256 else 0 := by
  by_cases hd : monsterNortonLine01SourceCodeSupport d
  · have hl : monsterNortonLine01ShortInputCode (monsterNortonLine01SourceCodeLookup d) = d := hd
    have h := monsterNortonLine01EleventhOdd_source_coefficients
      (monsterNortonLine01SourceCodeLookup d) i
    rw [hl] at h
    exact h
  · have he : d ≠ 82 := by
      intro h
      subst d
      have hc : monsterNortonLine01ShortInputCode 50 = 82 := by decide +kernel
      exact hd (hc ▸ monsterNortonLine01SourceCodeSupport_label 50)
    rw [monsterNortonLine01EleventhOddInteger_source_zero d i hd,
      ite_eq_right (by rintro ⟨h, _⟩; exact he h)]

/-- The actual eleventh odd-short coordinate is half of the original X82 unit at column one. -/
theorem monsterNortonLine01EleventhOdd_actual (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra.symm (y555NortonActualU.val
      (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)))).2.1
        (Sum.inr (Sum.inr (d, i))) =
          if d = 82 ∧ i.val = 1 then (1 / 2 : ℝ) else 0 := by
  rw [monsterNortonLine01EleventhOddInteger_actual,
    monsterNortonLine01EleventhOddInteger_singleton]
  split_ifs <;> norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
