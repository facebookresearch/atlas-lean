/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual forward-half pairings for the original code-nine preferred short vector. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineForwardCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddHalfPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPositiveTensorPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUInversePhysicalCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem spin_dense : monsterNortonMixedOddSpinPacket 3 =
    nortonUIntegerEmbed (monsterNortonMixedOddSpinDense 3) := by
  rw [← monsterNortonMixedOddSpinNumerator_sparse, monsterNortonMixedOddSpinNumerator_dense]

private theorem phase_real :
    qSign (monsterNortonEvenShortInitialVPhase (monsterNortonMixedOddBasisIndex 3)) *
      monsterNortonEvenShortOddFifthCoefficient (monsterNortonMixedOddBasisIndex 3) =
        (monsterNortonCodeNineForwardPhase : ℝ) / (8 * Real.sqrt 2) := by
  change (-1 : ℝ) * ((qSign (golayMaskWeight (golayEncodedMask 692) / 4 : ℕ) /
    Real.sqrt 2) * (-1 / 8)) = _
  rw [monsterNortonCodeNineForwardPhase, nortonUIntegerSign_real]
  ring

/-- Every supported short coefficient of the whole actual forward-half word is exact. -/
theorem monsterNortonCodeNineForwardHalf_short_form (p : Fin 32 × Fin 8) :
    griessForm (monsterNortonMixedOddHalfPacket 3)
      (monsterNortonPureShort (monsterNortonCodeNineForwardShortIndex p)) =
        (monsterNortonCodeNineForwardShortCoefficient p.1 p.2 : ℝ) / 32 := by
  rw [monsterNortonMixedOddHalfPacket]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp only [monsterNortonCodeNineForwardShortIndex]
  rw [monsterNortonTensorPositivePacket_odd_form]
  rw [spin_dense]
  simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff]
  have hpos : monsterNortonEvenShortFirstUOddPosition (monsterNortonMixedOddBasisIndex 3) =
      2 := rfl
  rw [hpos]
  rw [monsterNortonUInversePhysical_basis]
  have hr : ((monsterNortonCodeNineForwardShortRead p : ℤ) : ℝ) =
      2 * (monsterNortonCodeNineForwardShortCoefficient p.1 p.2 : ℝ) := by
    exact_mod_cast monsterNortonCodeNineForwardShortRead_coefficient p
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [monsterNortonCodeNineForwardShortRead, Int.cast_mul, Int.cast_add,
    nortonUIntegerSign_real] at hr
  rw [← mul_assoc, phase_real]
  field_simp [hn]
  ring_nf
  rw [hs]
  simp only [Nat.add_comm 2048]
  linear_combination 32 * hr

/-- Every supported tensor coefficient of the whole actual forward-half word is exact. -/
theorem monsterNortonCodeNineForwardHalf_tensor_form (p : Fin 64 × Fin 8) :
    griessForm (monsterNortonMixedOddHalfPacket 3)
      (monsterNortonTensorUnit (monsterNortonCodeNineForwardTensorIndex p).1
        (monsterNortonCodeNineForwardTensorIndex p).2) =
        (monsterNortonCodeNineForwardTensorCoefficient p : ℝ) / (32 * Real.sqrt 2) := by
  rw [monsterNortonMixedOddHalfPacket]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    monsterNortonCodeNineForwardTensorIndex]
  rw [monsterNortonTensorPositivePacket_tensor_form, spin_dense]
  simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
    spinDictionaryCode, spinDictionaryLabel_coeff]
  have hpos : monsterNortonEvenShortFirstUOddPosition (monsterNortonMixedOddBasisIndex 3) =
      2 := rfl
  rw [hpos, monsterNortonUInversePhysical_basis]
  have hr : ((monsterNortonCodeNineForwardTensorRead p : ℤ) : ℝ) =
      2 * (monsterNortonCodeNineForwardTensorCoefficient p : ℝ) := by
    exact_mod_cast monsterNortonCodeNineForwardTensorRead_coefficient p
  simp only [monsterNortonCodeNineForwardTensorRead, Int.cast_mul, Int.cast_sub,
    Int.cast_ite, Int.cast_neg, Int.cast_one, nortonUIntegerSign_real] at hr
  rw [← mul_assoc, phase_real]
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hn]
  linear_combination 32 * hr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
