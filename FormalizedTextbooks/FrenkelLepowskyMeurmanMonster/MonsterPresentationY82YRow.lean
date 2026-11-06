/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual y82 candidate agrees with the literal source word on the Y dictionary row. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82Tensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddTheta

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Fourier conversion extracts the actual signed Y coordinate at the upper spin label. -/
theorem monsterY82_hadamard_encode_high (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    monsterSpinHadamard (fun t => (griessConwayEncode x).2.2 t i)
      (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) =
        (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
          (trialityBlocksEquiv x).2.2.2 1 (finProdFinEquiv (d,i)) := by
  rw [monsterSpinHadamard_apply]
  change (qSign (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ 11) *
      (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i +
    (griessConwayEncode x).2.2
      (golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + Pi.single 11 1) i) /
        Real.sqrt 2 = _
  rw [golayLabel_high_add_omega]
  simp only [griessConwayEncode, spinDictionaryCode_high, spinDictionaryCode_low,
    golayLabel_high_last, golayLabel_low_last, qSign_one, qSign_zero, one_mul]
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hs]
  rw [hsq]
  ring

/-- Fourier conversion cancels the first factor of the actual candidate on every tensor column. -/
theorem monsterY82_hadamard_encode_action (x : GriessSpace) (t : SpinIndex) (i : Fin 24) :
    monsterSpinHadamard
      (fun u => (griessConwayEncode (rhoLocal monsterSourceY82Local x)).2.2 u i) t =
        qSign (golayEncoder monsterSourceY82Code i) * monsterSourceY82PlusMinus.val
          (monsterSpinHadamard (fun u => (griessConwayEncode x).2.2 u i)) t := by
  have hf : (fun u => (griessConwayEncode (rhoLocal monsterSourceY82Local x)).2.2 u i) =
      qSign (golayEncoder monsterSourceY82Code i) •
        monsterSourceY82Spin.val (fun u => (griessConwayEncode x).2.2 u i) := by
    funext u
    exact monsterSourceY82_encode_tensor x u i
  rw [hf, map_smul]
  change qSign (golayEncoder monsterSourceY82Code i) *
    monsterSpinHadamard (monsterSpinHadamard (monsterSourceY82PlusMinus.val
      (monsterSpinHadamard (fun u => (griessConwayEncode x).2.2 u i)))) t = _
  rw [monsterSpinHadamard_involutive]

/-- The upper source spin label has the primary source Y phase and no relabeling. -/
theorem monsterY82_plusminus_high (f : SpinSpace) (d : Fin 2048) :
    monsterSourceY82PlusMinus.val f (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) =
      qSign (spinDot (sourceWordTheta ⟨d.val, by omega⟩) monsterSourceY82Code +
        spinDot (sourceCodeThetaPolynomial monsterSourceY82Code)
          (golayLabelCoefficients ⟨d.val, by omega⟩)) *
            f (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) := by
  rw [monsterSourceY82PlusMinus_apply, golayLabel_high_last]
  have h11 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [h11, zero_smul, add_zero, one_mul]
  have hθ : spinDot (sourceCodeThetaPolynomial monsterSourceY82Code) (Pi.single 11 1) = 0 := by
    change spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients 82))
      (Pi.single 11 1) = 0
    rw [← sourceWordTheta_eq_polynomial]
    exact sourceWordTheta_dot_omega 82
  rw [← golayLabel_low_add_omega, sourceCodeThetaPolynomial_add_omega,
    spinDot_add_right, hθ, add_zero, ← sourceWordTheta_eq_polynomial]

/-- The candidate's actual Y row matches the literal triality-conjugated x82 word. -/
theorem monsterSourceY82_blocks_Y_match (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv (rhoLocal monsterSourceY82Local x)).2.2.2 1
      (finProdFinEquiv (d,i)) =
    (trialityBlocksEquiv
      ((sExtra * rhoLocal (inclQ (sourceQCode 82 0)) * sExtra⁻¹) x)).2.2.2 1
        (finProdFinEquiv (d,i)) := by
  have h := monsterY82_hadamard_encode_action x
    (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i
  rw [monsterY82_hadamard_encode_high, monsterY82_plusminus_high,
    monsterY82_hadamard_encode_high] at h
  rw [monsterSourceYWord_blocks_Y]
  rw [spinDot_comm (golayLabelCoefficients 82) (sourceWordTheta ⟨d.val, by omega⟩),
    spinDot_comm (golayLabelCoefficients ⟨d.val, by omega⟩)
      (sourceCodeThetaPolynomial (golayLabelCoefficients 82)), qSign_add]
  change _ = qSign (_ + _) * qSign (golayEncoder monsterSourceY82Code i) * _
  simp only [monsterSourceY82Code] at h ⊢
  split_ifs at h <;> nlinarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
