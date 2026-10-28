/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact inverse triality on every actual sixty-four-dimensional octad block. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual inverse extra preserves each original octad block by the inverse Fourier/sign action. -/
theorem monsterNortonOctadShortVector_extra_inverse (d : Fin 759) (v : Fin 64 → ℝ) :
    sExtra.symm (monsterNortonOctadShortVector d v) =
      monsterNortonOctadShortVector d (trialityOctadAction.symm v) := by
  apply sExtra.injective
  rw [LinearEquiv.apply_symm_apply, monsterNortonOctadShortVector_extra,
    LinearEquiv.apply_symm_apply]

/-- The exact integer inverse coefficient retains the sign on the input octad coordinate. -/
def monsterNortonOctadInverseCoefficient (r s : Fin 64) : ℤ :=
  (if trialityBitWeight8 (trialityEvenMask s) / 2 % 2 = 0 then 1 else -1) *
    trialityHadamard r s

/-- Each actual inverse octad Fourier row is this integer numerator divided by eight. -/
theorem monsterNortonOctadTriality_inverse_single (e k : Fin 64) (c : ℝ) :
    trialityOctadAction.symm (Pi.single e c) k =
      (monsterNortonOctadInverseCoefficient k e : ℝ) / 8 * c := by
  change (trialityNormalizedHadamard *ᵥ (fun r =>
    (if trialityBitWeight8 (trialityEvenMask r) / 2 % 2 = 0 then (1 : ℝ) else -1)⁻¹ *
      ((Pi.single e c : Fin 64 → ℝ) r))) k = _
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, trialityNormalizedHadamard,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, monsterNortonOctadInverseCoefficient,
    Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_neg]
  have hcast : (Int.castRingHom ℝ) (trialityHadamard k e) =
      (trialityHadamard k e : ℝ) := rfl
  rw [hcast]
  split_ifs <;> norm_num <;> (ring_nf; try simp)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
