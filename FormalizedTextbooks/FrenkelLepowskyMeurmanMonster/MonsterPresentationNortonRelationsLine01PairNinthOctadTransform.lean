/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete actual inverse-triality action on both reached eighth octad rows. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairNinthOctadData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadShortLinear

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original octad index for each of the two reached eighth-state source codes. -/
noncomputable def monsterNortonLine01PairEighthBlockOctad (a : Fin 2) : Fin 759 :=
  monsterNortonOctadIndex (monsterNortonLine01PairEighthOctadCodes a)
    (monsterNortonLine01PairEighthOctad_weight a)

private theorem finiteExpansion (v : Fin 64 → ℝ) :
    v = ∑ e : Fin 64, v e • Pi.single e 1 := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Both full actual inverse octad rows are exactly minus one half of their surviving unit. -/
theorem monsterNortonLine01PairNinthOctad_row (a : Fin 2) :
    trialityOctadAction.symm
      (fun r => (monsterNortonLine01PairEighthOctadNumerator a r : ℝ) / 16) =
      (-1 / 2 : ℝ) • Pi.single (monsterNortonLine01PairNinthOctadTarget a) 1 := by
  conv_lhs =>
    rw [finiteExpansion (fun r => (monsterNortonLine01PairEighthOctadNumerator a r : ℝ) / 16)]
  rw [map_sum]
  simp only [map_smul]
  funext r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    monsterNortonOctadTriality_inverse_single, mul_one]
  calc
    _ = ((∑ s : Fin 64, monsterNortonLine01PairEighthOctadNumerator a s *
      monsterNortonOctadInverseCoefficient r s : ℤ) : ℝ) / 128 := by
      rw [Int.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      rw [Int.cast_mul]
      ring
    _ = _ := by
      rw [monsterNortonLine01PairNinthOctadNumerator_certificate]
      simp only [Int.cast_ite, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, Pi.single_apply]
      by_cases h : r = monsterNortonLine01PairNinthOctadTarget a
      · subst r
        norm_num
      · simp [h]

/-- Each entire reached Griess octad vector has its exact inverse-triality image. -/
theorem monsterNortonLine01PairNinthOctad_vector (a : Fin 2) :
    sExtra.symm
      (monsterNortonOctadShortVector (monsterNortonLine01PairEighthBlockOctad a)
      (fun r => (monsterNortonLine01PairEighthOctadNumerator a r : ℝ) / 16)) =
      (-1 / 2 : ℝ) • monsterNortonPureShort
        (Sum.inr (Sum.inl (monsterNortonLine01PairEighthBlockOctad a,
          monsterNortonLine01PairNinthOctadTarget a))) := by
  rw [monsterNortonOctadShortVector_extra_inverse, monsterNortonLine01PairNinthOctad_row,
    monsterNortonOctadShortVector_smul, monsterNortonOctadShortVector_single]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
