/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite support pairings identify the entire actual second-input forward half. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondCoefficientData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Integer coefficient numerator of each genuine sparse candidate unit. -/
def monsterNortonSecondHalfNumerator : NortonSecondHalfIndex → ℤ
  | Sum.inl i => monsterNortonSecondHalfPairCoefficient i
  | Sum.inr (Sum.inl _) => -1
  | Sum.inr (Sum.inr (d, e)) => monsterNortonSecondHalfOctadCoefficient d e

/-- Integer source norm weights, two for A and C and one for octad units. -/
def monsterNortonSecondHalfIntegerWeight : NortonSecondHalfIndex → ℤ
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl _) => 2
  | Sum.inr (Sum.inr _) => 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Verify the 240 support pairings as exact finite integer sums.
/-- Every support pairing has its exact signed numerator from all sixty-four actual terms. -/
theorem monsterNortonSecondHalfPairings_integer (i : NortonSecondHalfIndex) :
    (∑ e : Fin 64, monsterNortonSecondSixthInteger e * monsterNortonSecondHalfGram e i) =
      -4 * monsterNortonSecondHalfNumerator i * monsterNortonSecondHalfIntegerWeight i := by
  revert i
  decide +kernel

private theorem coefficient_weight (i : NortonSecondHalfIndex) :
    monsterNortonSecondHalfCoefficient i * monsterNortonSecondHalfWeight i =
      (monsterNortonSecondHalfNumerator i : ℝ) *
        (monsterNortonSecondHalfIntegerWeight i : ℝ) / 16 := by
  rcases i with i | (i | ⟨d, e⟩) <;>
    simp only [monsterNortonSecondHalfCoefficient, monsterNortonSecondHalfWeight,
      monsterNortonSecondHalfNumerator, monsterNortonSecondHalfIntegerWeight] <;> push_cast <;>
    ring

/-- Every actual seventh-step support pairing equals the complete candidate's coefficient weight. -/
theorem monsterNortonSecondHalfPairings_actual (i : NortonSecondHalfIndex) :
    griessForm (qSign (monsterNortonEvenShortInitialVPhase 1) •
      monsterNortonEvenShortSecondSeventhPacket) (monsterNortonSecondHalfVector i) =
      monsterNortonSecondHalfCoefficient i * monsterNortonSecondHalfWeight i := by
  have hv : monsterNortonEvenShortInitialVPhase (1 : Fin 23) = 1 := by decide +kernel
  rw [hv, qSign_one]
  unfold monsterNortonEvenShortSecondSeventhPacket
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hs : griessForm
      (∑ e : Fin 64, monsterNortonEvenShortSecondSixthCoefficient e •
        monsterNortonEvenShortSecondSeventhTerm e) (monsterNortonSecondHalfVector i) =
      ∑ e : Fin 64, monsterNortonEvenShortSecondSixthCoefficient e *
        griessForm (monsterNortonEvenShortSecondSeventhTerm e)
          (monsterNortonSecondHalfVector i) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hs]
  simp_rw [monsterNortonSecondSixthCoefficient_integer, monsterNortonSecondHalfGram_actual]
  have ht : (∑ e : Fin 64, (monsterNortonSecondSixthInteger e : ℝ) / 8 *
      ((monsterNortonSecondHalfGram e i : ℝ) / 8)) =
      ((∑ e : Fin 64, monsterNortonSecondSixthInteger e *
        monsterNortonSecondHalfGram e i : ℤ) : ℝ) / 64 := by
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [ht, monsterNortonSecondHalfPairings_integer, coefficient_weight]
  push_cast
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
