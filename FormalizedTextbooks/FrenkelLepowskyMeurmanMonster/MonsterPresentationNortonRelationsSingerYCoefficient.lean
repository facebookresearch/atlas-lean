/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A genuine nonzero Fourier coefficient fixes the scalar sign in source Y covariance. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCrossPhase

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem omega_theta_zero :
    sourceCodeThetaPolynomial (Pi.single 11 1) = 0 := by
  rw [sourceCodeThetaPolynomial_single]
  have h : ∀ j, sourceCodeTheta 11 j = 0 := by decide +kernel
  funext j
  exact h j

private theorem low_theta_omega_zero (a : Fin 2048) :
    spinDot (sourceCodeThetaPolynomial (monsterNortonYCode a)) (Pi.single 11 1) = 0 := by
  change spinDot (sourceCodeThetaPolynomial
    (golayLabelCoefficients ⟨a.val, by omega⟩)) (Pi.single 11 1) = 0
  rw [← sourceWordTheta_eq_polynomial]
  exact sourceWordTheta_dot_omega _

private theorem low_code_ne_zero (a : Fin 2048) (ha : a ≠ 0) : monsterNortonYCode a ≠ 0 := by
  intro h
  have hz : golayLabelCoefficients (0 : Fin 4096) = 0 := by
    funext j
    have h : ∀ j, golayLabelCoefficients (0 : Fin 4096) j = 0 := by decide +kernel
    exact h j
  have hd : (⟨a.val, by omega⟩ : Fin 4096) = 0 :=
    golayLabelCoefficients_bijective.injective (h.trans hz.symm)
  apply ha
  apply Fin.ext
  exact congrArg (fun d : Fin 4096 => d.val) hd

private theorem hadamard_zero_low (t : SpinIndex) (ht : t 11 = 0) (hne : t ≠ 0) :
    monsterSpinHadamard (Pi.single (0 : SpinIndex) 1) t = 0 := by
  have hf : monsterSpinOmegaFlip t ≠ 0 := by
    intro h
    have he := congrFun h 11
    change t 11 + 1 = 0 at he
    rw [ht, zero_add] at he
    exact one_ne_zero he
  simp [monsterSpinHadamard_apply, hne, hf]

/-- Every nonzero low-code Y operator has the same genuine positive zero-coordinate coefficient. -/
theorem monsterNortonYSpin_zero_coefficient (a : Fin 2048) (ha : a ≠ 0) :
    (monsterNortonYSpin a).val (Pi.single (0 : SpinIndex) 1) 0 = (1 / 2 : ℝ) := by
  have ha0 := low_code_ne_zero a ha
  have hf0 : monsterSpinOmegaFlip (0 : SpinIndex) = Pi.single 11 1 := by
    simp [monsterSpinOmegaFlip, monsterSpinOmegaVector]
  have hlast : (Pi.single 11 (1 : ZMod 2) : SpinIndex) 11 = 1 := by simp
  have hom : (Pi.single 11 (1 : ZMod 2) : SpinIndex) ≠ 0 := by
    intro h
    have he := congrFun h 11
    simp at he
  change monsterSpinHadamard ((monsterNortonYPlusMinus a).val
    (monsterSpinHadamard (Pi.single (0 : SpinIndex) 1))) 0 = _
  rw [monsterSpinHadamard_apply, hf0, monsterNortonYPlusMinus_apply,
    monsterNortonYPlusMinus_apply]
  simp only [Pi.zero_apply, qSign_zero, one_mul, sourceCodeThetaPolynomial_zero,
    spinDot_zero_left, spinDot_zero_right, zero_add, zero_mul, zero_smul,
    zero_add, one_smul, hlast, omega_theta_zero, low_theta_omega_zero,
    CharTwo.add_self_eq_zero, add_zero]
  rw [hadamard_zero_low _ (monsterNortonYCode_last a) ha0, monsterSpinHadamard_apply]
  rw [show monsterSpinOmegaFlip (Pi.single 11 1) = (0 : SpinIndex) from by
    rw [← hf0, monsterSpinOmegaFlip_double]]
  simp [hom]
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
