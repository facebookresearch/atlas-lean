/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full tensor dictionary for all low source y codes, with the actual quarter-weight phase. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYSpinTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
variable (a : Fin 2048)

/-- The positive source code retains its quarter-weight central phase at upper spin labels. -/
theorem monsterNortonY_sourceCode_phase_high (d : Fin 2048) :
    spinPhase (sourceQCode ⟨a.val, by omega⟩ 0)
      (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) =
    (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) +
      spinDot (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
        (golayLabelCoefficients ⟨d.val, by omega⟩) := by
  rw [spinPhase, sourceQCode_modulation, ← golayLabel_low_add_omega, spinDot_add_right]
  have h : spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients ⟨a.val, by omega⟩))
      (Pi.single 11 1) = 0 := by
    rw [← sourceWordTheta_eq_polynomial]
    exact sourceWordTheta_dot_omega ⟨a.val, by omega⟩
  rw [h, add_zero]
  change ((0 : ZMod 2) + (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ)) +
    spinDot (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
      (golayLabelCoefficients ⟨d.val, by omega⟩) = _
  rw [zero_add]

/-- The source code code action on Y has its exact theta and physical-coordinate signs. -/
theorem monsterNortonY_sourceCode_blocks_Y
    (x : GriessSpace)
    (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) x)).2.2.2 1
      (finProdFinEquiv (d,i)) =
        qSign (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) *
          qSign (golayEncoder (monsterNortonEvenCodeVector a) i) *
          qSign (spinDot
        (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
            (golayLabelCoefficients ⟨d.val, by omega⟩)) *
              (trialityBlocksEquiv x).2.2.2 1
                (finProdFinEquiv ((monsterNortonEvenCodeSum a) d,i)) := by
  have h := (monsterNortonEven_sourceCode_hadamard_tensor a) x
    (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i
  rw [monsterY82_hadamard_encode_high, monsterMonomialSpinRepresentation_apply,
    monsterNortonY_sourceCode_phase_high, sourceQCode_translation] at h
  change _ = qSign ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) + spinDot
        (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
      (golayLabelCoefficients ⟨d.val, by omega⟩)) *
    monsterSpinHadamard (fun u => (griessConwayEncode x).2.2 u i)
      (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + (monsterNortonEvenCodeVector a)) at h
  rw [← (monsterNortonEvenCodeSum_high a), monsterY82_hadamard_encode_high,
    ← golayEncoder_low_qSign, ← golayEncoder_low_qSign, (monsterNortonEvenCodeSum_low a),
    map_add, Pi.add_apply, qSign_add] at h
  simp only [qSign_add] at h
  have hsq := qSign_sq (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i)
  calc
    _ = qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i) *
        (qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i) *
          (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) x)).2.2.2 1
            (finProdFinEquiv (d,i))) := by rw [← mul_assoc, hsq, one_mul]
    _ = (qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i) *
        qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i)) *
          (qSign (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) *
            qSign (golayEncoder (monsterNortonEvenCodeVector a) i) *
            qSign (spinDot
        (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
              (golayLabelCoefficients ⟨d.val, by omega⟩)) *
                (trialityBlocksEquiv x).2.2.2 1
                  (finProdFinEquiv ((monsterNortonEvenCodeSum a) d,i))) := by rw [h]; ring
    _ = _ := by rw [hsq, one_mul]

/-- Literal source y has its exact lower-row quarter-weight, sign, and translation factors. -/
theorem monsterNortonYAllWord_blocks_Z (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv
      ((sExtra * rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) * sExtra⁻¹) x)).2.2.2 2
        (finProdFinEquiv (d,i)) =
      qSign (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) *
        qSign (golayEncoder (monsterNortonEvenCodeVector a) i) *
          qSign (spinDot (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
            (golayLabelCoefficients ⟨d.val, by omega⟩)) *
              (trialityBlocksEquiv x).2.2.2 2
                (finProdFinEquiv (monsterNortonEvenCodeSum a d,i)) := by
  have hs : trialityCycle.symm 2 = 1 := by decide +kernel
  have hf : trialityCycle 1 = 2 := by decide +kernel
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, monsterTriality_XYZ_blocks, hs,
    monsterNortonY_sourceCode_blocks_Y, monsterTriality_inverse_XYZ_blocks, hf]

/-- Parker polarization retains precisely the quarter-weight of the source code. -/
theorem monsterNortonYAll_phase (d : Fin 2048) :
    ((golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ZMod 2) +
      (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) +
        spinDot (sourceWordTheta ⟨a.val, by omega⟩) (golayLabelCoefficients ⟨d.val, by omega⟩) =
    spinDot (sourceWordTheta ⟨d.val, by omega⟩) (monsterNortonEvenCodeVector a) +
      (golayMaskWeight (golayEncodedMask (monsterNortonEvenCodeSum a d).val) / 4 : ℕ) := by
  have h := sourceWordTheta_cross_dot ⟨d.val, by omega⟩ ⟨a.val, by omega⟩
    ⟨(monsterNortonEvenCodeSum a d).val, by omega⟩ (monsterNortonEvenCodeSum_low a d)
  change spinDot (sourceWordTheta ⟨d.val, by omega⟩) (monsterNortonEvenCodeVector a) +
    spinDot (sourceWordTheta ⟨a.val, by omega⟩) (golayLabelCoefficients ⟨d.val, by omega⟩) =
    (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) +
      (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) -
        (golayMaskWeight (golayEncodedMask (monsterNortonEvenCodeSum a d).val) / 4 : ℕ) at h
  linear_combination (norm := skip) h
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, sub_zero, add_zero]

/-- Every low Fourier label matches, including codes of odd quarter-weight. -/
theorem monsterNortonYAllWord_fourier_low (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    monsterSpinHadamard (fun t => (griessConwayEncode
      ((sExtra * rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) * sExtra⁻¹) x)).2.2 t i)
      (golayLabelCoefficients ⟨d.val, by omega⟩) =
    qSign (golayEncoder (monsterNortonYCode a) i) *
      (monsterNortonYPlusMinus a).val
        (monsterSpinHadamard (fun t => (griessConwayEncode x).2.2 t i))
          (golayLabelCoefficients ⟨d.val, by omega⟩) := by
  rw [monsterY82_hadamard_encode_low, monsterNortonYAllWord_blocks_Z,
    monsterNortonYPlusMinus_low, monsterY82_hadamard_encode_low]
  have h := monsterNortonYAll_phase a d
  rw [sourceWordTheta_eq_polynomial] at h
  have hsign := congrArg qSign h
  simp only [qSign_add] at hsign
  simp only [monsterNortonYCode, monsterNortonEvenCodeVector] at hsign ⊢
  calc
    _ = qSign (golayEncoder (golayLabelCoefficients ⟨a.val, by omega⟩) i) *
      ((qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        qSign (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) *
          qSign (spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients ⟨a.val, by omega⟩))
            (golayLabelCoefficients ⟨d.val, by omega⟩))) *
              (trialityBlocksEquiv x).2.2.2 2
                (finProdFinEquiv (monsterNortonEvenCodeSum a d,i))) := by ring
    _ = _ := by rw [hsign]; ring

/-- Every actual tensor column of the literal y-code word is the stated explicit spin operator. -/
theorem monsterNortonYAllWord_tensor
    (x : GriessSpace) (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode
      ((sExtra * rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) * sExtra⁻¹) x)).2.2 t i =
    qSign (golayEncoder (monsterNortonYCode a) i) *
      (monsterNortonYSpin a).val (fun u => (griessConwayEncode x).2.2 u i) t := by
  have h : monsterSpinHadamard (fun t => (griessConwayEncode
      ((sExtra * rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) * sExtra⁻¹) x)).2.2 t i) =
    monsterSpinHadamard (qSign (golayEncoder (monsterNortonYCode a) i) •
      (monsterNortonYSpin a).val (fun u => (griessConwayEncode x).2.2 u i)) := by
    funext u
    rw [map_smul]
    change _ = qSign (golayEncoder (monsterNortonYCode a) i) * _
    rw [monsterNortonYSpin_fourier]
    rcases spinDictionaryIndex_cases u with hu | hu
    · rw [hu]
      exact monsterNortonYAllWord_fourier_low a x (spinDictionaryCode u) i
    · rw [hu]
      exact monsterNortonYWord_fourier_high a x (spinDictionaryCode u) i
  have he := congrArg monsterSpinHadamard h
  rw [monsterSpinHadamard_involutive, monsterSpinHadamard_involutive] at he
  exact congrFun he t

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
