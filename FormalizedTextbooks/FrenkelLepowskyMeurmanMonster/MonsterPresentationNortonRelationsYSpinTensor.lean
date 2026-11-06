/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact tensor-column dictionary for arbitrary low source y codes of quarter-weight parity zero. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCodePhases

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
variable (a : Fin 2048)

/-- The upper source spin label has the primary source Y phase and no relabeling. -/
theorem monsterNortonYPlusMinus_high (f : SpinSpace) (d : Fin 2048) :
    (monsterNortonYPlusMinus a).val f (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) =
      qSign (spinDot (sourceWordTheta ⟨d.val, by omega⟩) (monsterNortonYCode a) +
        spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a))
          (golayLabelCoefficients ⟨d.val, by omega⟩)) *
            f (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) := by
  rw [monsterNortonYPlusMinus_apply, golayLabel_high_last]
  have h11 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [h11, zero_smul, add_zero, one_mul]
  have hθ : spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a)) (Pi.single 11 1) = 0 := by
    change spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients ⟨a.val, by omega⟩))
      (Pi.single 11 1) = 0
    rw [← sourceWordTheta_eq_polynomial]
    exact sourceWordTheta_dot_omega ⟨a.val, by omega⟩
  rw [← golayLabel_low_add_omega, sourceCodeThetaPolynomial_add_omega,
    spinDot_add_right, hθ, add_zero, ← sourceWordTheta_eq_polynomial]

/-- The literal source y-code word has this actual Z-row formula. -/
theorem monsterNortonYWord_blocks_Z
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (x : GriessSpace)
    (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv
      ((sExtra * rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) * sExtra⁻¹) x)).2.2.2 2
        (finProdFinEquiv (d,i)) =
      qSign (golayEncoder (monsterNortonYCode a) i) *
        qSign (spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a))
          (golayLabelCoefficients ⟨d.val, by omega⟩)) *
            (trialityBlocksEquiv x).2.2.2 2
              (finProdFinEquiv ((monsterNortonEvenCodeSum a) d,i)) := by
  have hs : trialityCycle.symm 2 = 1 := by decide +kernel
  have hf : trialityCycle 1 = 2 := by decide +kernel
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, monsterTriality_XYZ_blocks, hs,
    monsterNortonEven_sourceCode_blocks_Y a ha, monsterTriality_inverse_XYZ_blocks, hf]
  rfl

/-- The candidate's lower plus/minus label has the exact source translation and theta phase. -/
theorem monsterNortonYPlusMinus_low (f : SpinSpace) (d : Fin 2048) :
    (monsterNortonYPlusMinus a).val f (golayLabelCoefficients ⟨d.val, by omega⟩) =
      qSign (spinDot (sourceWordTheta ⟨d.val, by omega⟩) (monsterNortonYCode a)) *
        f (golayLabelCoefficients ⟨((monsterNortonEvenCodeSum a) d).val, by omega⟩) := by
  rw [monsterNortonYPlusMinus_apply, golayLabel_low_last, zero_mul, add_zero,
    add_zero, one_smul]
  change qSign (spinDot (sourceCodeThetaPolynomial _) (monsterNortonEvenCodeVector a)) *
    f (_ + monsterNortonEvenCodeVector a) = _
  rw [← monsterNortonEvenCodeSum_low a, ← sourceWordTheta_eq_polynomial]
  rfl

/-- Fourier conjugation cancels the first factor of the explicit candidate. -/
theorem monsterNortonYSpin_fourier (f : SpinSpace) (t : SpinIndex) :
    monsterSpinHadamard ((monsterNortonYSpin a).val f) t =
      (monsterNortonYPlusMinus a).val (monsterSpinHadamard f) t := by
  change monsterSpinHadamard (monsterSpinHadamard
    ((monsterNortonYPlusMinus a).val (monsterSpinHadamard f))) t = _
  rw [monsterSpinHadamard_involutive]

/-- The actual literal y-code word has the candidate's upper Fourier row. -/
theorem monsterNortonYWord_fourier_high (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    monsterSpinHadamard (fun t => (griessConwayEncode
      ((sExtra * rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) * sExtra⁻¹) x)).2.2 t i)
      (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) =
    qSign (golayEncoder (monsterNortonYCode a) i) *
      (monsterNortonYPlusMinus a).val
        (monsterSpinHadamard (fun t => (griessConwayEncode x).2.2 t i))
          (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) := by
  rw [monsterY82_hadamard_encode_high, monsterSourceYWord_blocks_Y,
    monsterNortonYPlusMinus_high, monsterY82_hadamard_encode_high]
  simp only [monsterNortonYCode, qSign_add]
  rw [spinDot_comm (golayLabelCoefficients ⟨a.val, by omega⟩)
    (sourceWordTheta ⟨d.val, by omega⟩),
    spinDot_comm (golayLabelCoefficients ⟨d.val, by omega⟩)
      (sourceCodeThetaPolynomial (golayLabelCoefficients ⟨a.val, by omega⟩))]
  ring

/-- The lower Fourier row matches with the genuine Parker quarter-weight corrections. -/
theorem monsterNortonYWord_fourier_low
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0)
    (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    monsterSpinHadamard (fun t => (griessConwayEncode
      ((sExtra * rhoLocal (inclQ (sourceQCode ⟨a.val, by omega⟩ 0)) * sExtra⁻¹) x)).2.2 t i)
      (golayLabelCoefficients ⟨d.val, by omega⟩) =
    qSign (golayEncoder (monsterNortonYCode a) i) *
      (monsterNortonYPlusMinus a).val
        (monsterSpinHadamard (fun t => (griessConwayEncode x).2.2 t i))
          (golayLabelCoefficients ⟨d.val, by omega⟩) := by
  rw [monsterY82_hadamard_encode_low, monsterNortonYWord_blocks_Z a ha,
    monsterNortonYPlusMinus_low, monsterY82_hadamard_encode_low]
  have h := monsterNortonEven_Z_phase a ha d
  rw [sourceWordTheta_eq_polynomial] at h
  have hsign := congrArg qSign h
  simp only [qSign_add] at hsign
  simp only [monsterNortonYCode, monsterNortonEvenCodeVector] at hsign ⊢
  rw [← hsign]
  have hsq := qSign_sq (golayMaskWeight
    (golayEncodedMask (monsterNortonEvenCodeSum a d).val) / 4 : ℕ)
  calc
    _ = (qSign (golayEncoder (golayLabelCoefficients ⟨a.val, by omega⟩) i) *
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      qSign (spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients ⟨a.val, by omega⟩))
        (golayLabelCoefficients ⟨d.val, by omega⟩)) *
      (trialityBlocksEquiv x).2.2.2 2
        (finProdFinEquiv (monsterNortonEvenCodeSum a d,i)))) * 1 := by ring
    _ = _ := by rw [← hsq]; ring

/-- Every actual tensor column of the literal y-code word is the stated explicit spin operator. -/
theorem monsterNortonYWord_tensor
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0)
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
      exact monsterNortonYWord_fourier_low a ha x (spinDictionaryCode u) i
    · rw [hu]
      exact monsterNortonYWord_fourier_high a x (spinDictionaryCode u) i
  have he := congrArg monsterSpinHadamard h
  rw [monsterSpinHadamard_involutive, monsterSpinHadamard_involutive] at he
  exact congrFun he t

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
