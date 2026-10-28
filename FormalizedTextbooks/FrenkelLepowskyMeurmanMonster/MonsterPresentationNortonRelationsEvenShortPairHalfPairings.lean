/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact real support pairings of twelve complete actual forward-half packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfPairingsData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem coefficient_weight (k : Fin 12) (i : NortonPairHalfIndex) :
    monsterNortonPairHalfCoefficient k i * monsterNortonPairHalfWeight i =
      (monsterNortonPairHalfNumerator k i : ℝ) *
        (monsterNortonPairHalfIntegerWeight i : ℝ) / 16 := by
  rcases i with i | (i | ⟨d, e⟩) <;>
    simp only [monsterNortonPairHalfCoefficient, monsterNortonPairHalfWeight,
      monsterNortonPairHalfNumerator, monsterNortonPairHalfIntegerWeight] <;> push_cast <;>
    ring

private theorem scaled_integer_sum (k : Fin 12) (i : NortonPairHalfIndex) :
    (∑ e : Fin 64, (monsterNortonPairHalfSixthInteger k e : ℝ) / 8 *
      ((monsterNortonPairHalfGram k e i : ℤ) : ℝ) / 8) =
        ((∑ e : Fin 64, monsterNortonPairHalfSixthInteger k e *
          monsterNortonPairHalfGram k e i : ℤ) : ℝ) / 64 := by
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Whole actual seventh-packet support pairings equal the genuine source coefficient weights. -/
theorem monsterNortonPairHalfPairings_actual (k : Fin 12) (i : NortonPairHalfIndex) :
    griessForm (qSign (monsterNortonEvenShortInitialVPhase (monsterNortonPairHalfBasisIndex k)) •
      monsterNortonEvenShortSeventhPacket (monsterNortonPairHalfBasisIndex k))
        (monsterNortonPairHalfVector k i) =
      monsterNortonPairHalfCoefficient k i * monsterNortonPairHalfWeight i := by
  rw [monsterNortonPairHalfInitialSign_actual, monsterNortonPairHalf_seventh_sum]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, map_sum, LinearMap.sum_apply]
  simp_rw [monsterNortonPairHalfSixthCoefficient_integer, monsterNortonPairHalfGram_actual]
  have hs : (∑ e : Fin 64, (monsterNortonPairHalfSixthInteger k e : ℝ) / 8 *
      ((monsterNortonPairHalfGram k e i : ℝ) / 8)) =
      ((∑ e : Fin 64, monsterNortonPairHalfSixthInteger k e *
        monsterNortonPairHalfGram k e i : ℤ) : ℝ) / 64 := by
    calc
      _ = ∑ e : Fin 64, (monsterNortonPairHalfSixthInteger k e : ℝ) / 8 *
        (monsterNortonPairHalfGram k e i : ℝ) / 8 := by
          apply Finset.sum_congr rfl
          intro e _
          ring
      _ = _ := scaled_integer_sum k i
  rw [hs, coefficient_weight]
  have hi := congrArg (fun z : ℤ => (z : ℝ)) (monsterNortonPairHalfPairings_integer k i)
  push_cast at hi
  push_cast
  linear_combination (1 / 64 : ℝ) * hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
