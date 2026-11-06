/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortThetaSplitCertificates

/-! The checked small tables are exactly the original Parker theta on every source label. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original theta polarization between the two six-coordinate source halves. -/
theorem generatedSeventhXiShortThetaPolynomial_two_halves (a b : Fin 6 → ZMod 2) :
    sourceCodeThetaPolynomial
        (Fin.append a (0 : Fin 6 → ZMod 2) + Fin.append (0 : Fin 6 → ZMod 2) b) =
      sourceCodeThetaPolynomial (Fin.append a (0 : Fin 6 → ZMod 2)) +
        sourceCodeThetaPolynomial (Fin.append (0 : Fin 6 → ZMod 2) b) +
        (fun k => ∑ i : Fin 6, ∑ j : Fin 6, a i * b j *
          golayBooleanCast
            ((parkerBasisAssociatorMasks (Fin.castAdd 6 i) (Fin.natAdd 6 j)).testBit k.val)) := by
  funext k
  change sourceCodeThetaPolynomial
      (Fin.append a (0 : Fin 6 → ZMod 2) + Fin.append (0 : Fin 6 → ZMod 2) b) k =
    sourceCodeThetaPolynomial (Fin.append a (0 : Fin 6 → ZMod 2)) k +
      sourceCodeThetaPolynomial (Fin.append (0 : Fin 6 → ZMod 2) b) k + _
  rw [sourceCodeThetaPolynomial_add_cross]
  apply congrArg (fun z : ZMod 2 =>
    sourceCodeThetaPolynomial (Fin.append a (0 : Fin 6 → ZMod 2)) k +
    sourceCodeThetaPolynomial (Fin.append (0 : Fin 6 → ZMod 2) b) k + z)
  have hlh (i j : Fin 6) : Fin.castAdd 6 i < Fin.natAdd 6 j := by
    change i.val < 6 + j.val
    omega
  have hhl (i j : Fin 6) : ¬ Fin.natAdd 6 i < Fin.castAdd 6 j := by
    change ¬ 6 + i.val < j.val
    omega
  simp only [Fin.sum_univ_add (a := 6) (b := 6), Fin.append_left, Fin.append_right,
    Pi.zero_apply, mul_zero, zero_mul, zero_add, add_zero, hlh, hhl, ite_true, ite_false,
    ite_self, Finset.sum_const_zero]

/-- The small evaluator gives every genuine original Parker theta coefficient, including omega. -/
theorem generatedSeventhXiShortThetaSplit_actual (d : Fin 4096) :
    sourceWordTheta d = golayLabelCoefficients (generatedSeventhXiShortThetaSplit d) := by
  have hm : sourceWordTheta d = sourceCodeThetaPolynomial (golayLabelCoefficients d) := by
    funext k
    exact sourceCodeThetaPolynomial_mask d k
  rw [hm, generatedSeventhXiShortTheta_code_split,
    generatedSeventhXiShortThetaPolynomial_two_halves,
    generatedSeventhXiShortThetaLow_polynomial, generatedSeventhXiShortThetaHigh_polynomial,
    generatedSeventhXiShortThetaSplit_coeff]
  apply congrArg (fun z : SpinIndex =>
    golayLabelCoefficients
        (generatedSeventhXiShortThetaLow (generatedSeventhXiShortThetaLowCode d)) +
      golayLabelCoefficients
        (generatedSeventhXiShortThetaHigh (generatedSeventhXiShortThetaHighCode d)) + z)
  funext k
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (generatedSeventhXiShortThetaLowCode d).val.testBit i.val = true
  · rw [ite_eq_left hi, generatedSeventhXiShortThetaCross_polynomial]
    simp [generatedSeventhXiShortCodeSix, hi, golayBooleanCast]
  · rw [ite_eq_right hi]
    simp [generatedSeventhXiShortCodeSix, hi, golayBooleanCast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
