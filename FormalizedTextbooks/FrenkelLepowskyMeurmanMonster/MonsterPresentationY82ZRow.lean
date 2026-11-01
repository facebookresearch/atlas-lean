/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact Z-row agreement of the source y82 candidate and literal triality word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82CodeTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Fourier conversion extracts the quarter-weight signed Z coordinate at the lower label. -/
theorem monsterY82_hadamard_encode_low (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    monsterSpinHadamard (fun t => (griessConwayEncode x).2.2 t i)
      (golayLabelCoefficients ⟨d.val, by omega⟩) =
        qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          (trialityBlocksEquiv x).2.2.2 2 (finProdFinEquiv (d,i)) := by
  rw [monsterSpinHadamard_apply]
  change (qSign (golayLabelCoefficients ⟨d.val, by omega⟩ 11) *
      (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
    (griessConwayEncode x).2.2
      (golayLabelCoefficients ⟨d.val, by omega⟩ + Pi.single 11 1) i) / Real.sqrt 2 = _
  rw [golayLabel_low_add_omega]
  simp only [griessConwayEncode, spinDictionaryCode_high, spinDictionaryCode_low,
    golayLabel_high_last, golayLabel_low_last, qSign_one, qSign_zero, one_mul]
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hs]
  rw [hsq]
  ring

/-- The source x82 code action on Y has its exact theta and physical-coordinate signs. -/
theorem monsterY82_sourceCode_blocks_Y (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode 82 0)) x)).2.2.2 1
      (finProdFinEquiv (d,i)) =
        qSign (golayEncoder monsterSourceY82Code i) *
          qSign (spinDot (sourceCodeThetaPolynomial monsterSourceY82Code)
            (golayLabelCoefficients ⟨d.val, by omega⟩)) *
              (trialityBlocksEquiv x).2.2.2 1 (finProdFinEquiv (monsterY82CodeSum d,i)) := by
  have h := monsterY82_sourceCode_hadamard_tensor x
    (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i
  rw [monsterY82_hadamard_encode_high, monsterMonomialSpinRepresentation_apply,
    monsterY82_sourceCode_phase_high, sourceQCode_translation] at h
  change _ = qSign (spinDot (sourceCodeThetaPolynomial monsterSourceY82Code)
      (golayLabelCoefficients ⟨d.val, by omega⟩)) *
    monsterSpinHadamard (fun u => (griessConwayEncode x).2.2 u i)
      (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + monsterSourceY82Code) at h
  rw [← monsterY82CodeSum_high, monsterY82_hadamard_encode_high,
    ← golayEncoder_low_qSign, ← golayEncoder_low_qSign, monsterY82CodeSum_low,
    map_add, Pi.add_apply, qSign_add] at h
  have hsq := qSign_sq (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i)
  calc
    _ = qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i) *
        (qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i) *
          (trialityBlocksEquiv (rhoLocal (inclQ (sourceQCode 82 0)) x)).2.2.2 1
            (finProdFinEquiv (d,i))) := by rw [← mul_assoc, hsq, one_mul]
    _ = (qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i) *
        qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) i)) *
          (qSign (golayEncoder monsterSourceY82Code i) *
            qSign (spinDot (sourceCodeThetaPolynomial monsterSourceY82Code)
              (golayLabelCoefficients ⟨d.val, by omega⟩)) *
                (trialityBlocksEquiv x).2.2.2 1
                  (finProdFinEquiv (monsterY82CodeSum d,i))) := by rw [h]; ring
    _ = _ := by rw [hsq, one_mul]

/-- The literal source y82 word has this actual Z-row formula. -/
theorem monsterY82_sourceWord_blocks_Z (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv
      ((sExtra * rhoLocal (inclQ (sourceQCode 82 0)) * sExtra⁻¹) x)).2.2.2 2
        (finProdFinEquiv (d,i)) =
      qSign (golayEncoder monsterSourceY82Code i) *
        qSign (spinDot (sourceCodeThetaPolynomial monsterSourceY82Code)
          (golayLabelCoefficients ⟨d.val, by omega⟩)) *
            (trialityBlocksEquiv x).2.2.2 2 (finProdFinEquiv (monsterY82CodeSum d,i)) := by
  have hs : trialityCycle.symm 2 = 1 := by decide +kernel
  have hf : trialityCycle 1 = 2 := by decide +kernel
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, monsterTriality_XYZ_blocks, hs,
    monsterY82_sourceCode_blocks_Y, monsterTriality_inverse_XYZ_blocks, hf]

/-- The candidate's lower plus/minus label has the exact source translation and theta phase. -/
theorem monsterY82_plusminus_low (f : SpinSpace) (d : Fin 2048) :
    monsterSourceY82PlusMinus.val f (golayLabelCoefficients ⟨d.val, by omega⟩) =
      qSign (spinDot (sourceWordTheta ⟨d.val, by omega⟩) monsterSourceY82Code) *
        f (golayLabelCoefficients ⟨(monsterY82CodeSum d).val, by omega⟩) := by
  rw [monsterSourceY82PlusMinus_apply, golayLabel_low_last, zero_mul, add_zero,
    add_zero, one_smul, ← monsterY82CodeSum_low, ← sourceWordTheta_eq_polynomial]

/-- Parker polarization cancels the two genuine quarter-weight corrections. -/
theorem monsterY82_Z_phase (d : Fin 2048) :
    ((golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ZMod 2) +
        spinDot (sourceWordTheta ⟨d.val, by omega⟩) monsterSourceY82Code +
        ((golayMaskWeight (golayEncodedMask (monsterY82CodeSum d).val) / 4 : ℕ) : ZMod 2) =
      spinDot (sourceCodeThetaPolynomial monsterSourceY82Code)
        (golayLabelCoefficients ⟨d.val, by omega⟩) := by
  have h := sourceWordTheta_cross_dot ⟨d.val, by omega⟩ 82
    ⟨(monsterY82CodeSum d).val, by omega⟩ (monsterY82CodeSum_low d)
  change spinDot (sourceWordTheta ⟨d.val, by omega⟩) monsterSourceY82Code +
      spinDot (sourceWordTheta 82) (golayLabelCoefficients ⟨d.val, by omega⟩) =
    (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) +
      (golayMaskWeight (golayEncodedMask 82) / 4 : ℕ) -
        (golayMaskWeight (golayEncodedMask (monsterY82CodeSum d).val) / 4 : ℕ) at h
  have he : ((golayMaskWeight (golayEncodedMask 82) / 4 : ℕ) : ZMod 2) = 0 := by decide +kernel
  rw [he, add_zero, sourceWordTheta_eq_polynomial 82] at h
  change _ = spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients 82))
    (golayLabelCoefficients ⟨d.val, by omega⟩)
  linear_combination (norm := skip) h
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, sub_zero]

/-- The candidate's actual Z row equals the literal source triality word. -/
theorem monsterSourceY82_blocks_Z_match (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (rhoLocal monsterSourceY82Local x)).2.2.2 2
      (finProdFinEquiv (d,i)) =
    (trialityBlocksEquiv
      ((sExtra * rhoLocal (inclQ (sourceQCode 82 0)) * sExtra⁻¹) x)).2.2.2 2
        (finProdFinEquiv (d,i)) := by
  have h := monsterY82_hadamard_encode_action x
    (golayLabelCoefficients ⟨d.val, by omega⟩) i
  rw [monsterY82_hadamard_encode_low, monsterY82_plusminus_low,
    monsterY82_hadamard_encode_low] at h
  rw [monsterY82_sourceWord_blocks_Z]
  have hphase : qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      qSign (spinDot (sourceWordTheta ⟨d.val, by omega⟩) monsterSourceY82Code) *
      qSign (golayMaskWeight (golayEncodedMask (monsterY82CodeSum d).val) / 4 : ℕ) =
        qSign (spinDot (sourceCodeThetaPolynomial monsterSourceY82Code)
          (golayLabelCoefficients ⟨d.val, by omega⟩)) := by
    rw [← qSign_add, ← qSign_add, monsterY82_Z_phase]
  have hsq := qSign_sq (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  calc
    _ = qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (trialityBlocksEquiv (rhoLocal monsterSourceY82Local x)).2.2.2 2
          (finProdFinEquiv (d,i))) := by rw [← mul_assoc, hsq, one_mul]
    _ = _ := by rw [h]; rw [← hphase]; ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
