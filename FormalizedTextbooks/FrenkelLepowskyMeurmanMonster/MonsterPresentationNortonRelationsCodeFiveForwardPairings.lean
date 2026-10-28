/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual forward-half pairings for the original code-five preferred short vector. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveForwardCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddHalfPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPositiveTensorPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUInversePhysicalCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem spin_dense : monsterNortonMixedOddSpinPacket 1 =
    nortonUIntegerEmbed (monsterNortonMixedOddSpinDense 1) := by
  rw [← monsterNortonMixedOddSpinNumerator_sparse, monsterNortonMixedOddSpinNumerator_dense]

private theorem phase_real :
    qSign (monsterNortonEvenShortInitialVPhase (monsterNortonMixedOddBasisIndex 1)) *
      monsterNortonEvenShortOddFifthCoefficient (monsterNortonMixedOddBasisIndex 1) =
        (monsterNortonCodeFiveForwardPhase : ℝ) / (8 * Real.sqrt 2) := by
  change (-1 : ℝ) * ((qSign (golayMaskWeight (golayEncodedMask 948) / 4 : ℕ) /
    Real.sqrt 2) * (-1 / 8)) = _
  rw [monsterNortonCodeFiveForwardPhase, nortonUIntegerSign_real]
  ring

/-- Every supported short coefficient of the whole actual forward-half word is exact. -/
theorem monsterNortonCodeFiveForwardHalf_short_form (p : Fin 32 × Fin 8) :
    griessForm (monsterNortonMixedOddHalfPacket 1)
      (monsterNortonPureShort (monsterNortonCodeFiveForwardShortIndex p)) =
        (monsterNortonCodeFiveForwardShortCoefficient p.1 p.2 : ℝ) / 32 := by
  rw [monsterNortonMixedOddHalfPacket]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp only [monsterNortonCodeFiveForwardShortIndex]
  rw [monsterNortonTensorPositivePacket_odd_form]
  rw [spin_dense]
  simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff]
  have hpos : monsterNortonEvenShortFirstUOddPosition (monsterNortonMixedOddBasisIndex 1) =
      3 := rfl
  rw [hpos]
  rw [monsterNortonUInversePhysical_basis]
  have hr : ((monsterNortonCodeFiveForwardShortRead p : ℤ) : ℝ) =
      2 * (monsterNortonCodeFiveForwardShortCoefficient p.1 p.2 : ℝ) := by
    exact_mod_cast monsterNortonCodeFiveForwardShortRead_coefficient p
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [monsterNortonCodeFiveForwardShortRead, Int.cast_mul, Int.cast_add,
    nortonUIntegerSign_real] at hr
  rw [← mul_assoc, phase_real]
  field_simp [hn]
  ring_nf
  rw [hs]
  simp only [Nat.add_comm 2048]
  linear_combination 32 * hr

/-- Every supported tensor coefficient of the whole actual forward-half word is exact. -/
theorem monsterNortonCodeFiveForwardHalf_tensor_form (p : Fin 64 × Fin 8) :
    griessForm (monsterNortonMixedOddHalfPacket 1)
      (monsterNortonTensorUnit (monsterNortonCodeFiveForwardTensorIndex p).1
        (monsterNortonCodeFiveForwardTensorIndex p).2) =
        (monsterNortonCodeFiveForwardTensorCoefficient p : ℝ) / (32 * Real.sqrt 2) := by
  rw [monsterNortonMixedOddHalfPacket]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    monsterNortonCodeFiveForwardTensorIndex]
  rw [monsterNortonTensorPositivePacket_tensor_form, spin_dense]
  simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
    spinDictionaryCode, spinDictionaryLabel_coeff]
  have hpos : monsterNortonEvenShortFirstUOddPosition (monsterNortonMixedOddBasisIndex 1) =
      3 := rfl
  rw [hpos, monsterNortonUInversePhysical_basis]
  have hr : ((monsterNortonCodeFiveForwardTensorRead p : ℤ) : ℝ) =
      2 * (monsterNortonCodeFiveForwardTensorCoefficient p : ℝ) := by
    exact_mod_cast monsterNortonCodeFiveForwardTensorRead_coefficient p
  simp only [monsterNortonCodeFiveForwardTensorRead, Int.cast_mul, Int.cast_sub,
    Int.cast_ite, Int.cast_neg, Int.cast_one, nortonUIntegerSign_real] at hr
  rw [← mul_assoc, phase_real]
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hn]
  linear_combination 32 * hr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
