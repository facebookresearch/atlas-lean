/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual OYY and OZZ cubic coefficients, separated into source spin and signed matrix factors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOctadXYZCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPairQProducts

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

def octadSpinLow (f : Fin 2048) : SpinIndex := golayLabelCoefficients ⟨f.val, by omega⟩
def octadSpinCode (o : Fin 759) : SpinIndex := golayLabelCoefficients (golayOctadLabel o)
noncomputable def octadSpinSelector (o : Fin 759) (d f : Fin 2048) : ℝ :=
  if spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d then 1 else 0
noncomputable def octadYSpinConstant (o : Fin 759) (d f : Fin 2048) (i j : Fin 24) : ℝ :=
  qSign (spinDot (sourceWordTheta (golayOctadLabel o)) (octadSpinLow f)) *
    qSign ((octadSpinLow f + octadSpinCode o) 11) *
    (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
    (if (golayEncodedMask f.val).testBit j.val then -1 else 1) * octadSpinSelector o d f
noncomputable def octadZSpinConstant (o : Fin 759) (d f : Fin 2048) : ℝ :=
  qSign (spinDot (sourceWordTheta (golayOctadLabel o)) (octadSpinLow f)) *
    qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
    qSign (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) * octadSpinSelector o d f
noncomputable def octadNegativeCharacter (o : Fin 759) (e : Fin 64) (f : Fin 2048) : ℝ :=
  qSign (spinDot
    (golaySyndrome (integerParity (griessOctadNegativeInteger o e))) (octadSpinLow f))

private theorem source_Y_omega (d : Fin 2048) (i : Fin 24) (t : SpinIndex) (c : ZMod 2) :
    trialityYSpin d i (t + c • Pi.single 11 1) = qSign c * trialityYSpin d i t := by
  rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide +kernel) c with rfl | rfl
  · simp only [zero_smul, add_zero, qSign_zero, one_mul]
  · simpa only [one_smul, qSign_one, neg_one_mul, trialitySpinOmega] using
      trialityYSpin_omega d i t
private theorem source_Z_omega (d : Fin 2048) (t : SpinIndex) (c : ZMod 2) :
    trialityZSpin d (t + c • Pi.single 11 1) = trialityZSpin d t := by
  rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide +kernel) c with rfl | rfl
  · simp only [zero_smul, add_zero]
  · simpa only [one_smul, trialitySpinOmega] using trialityZSpin_omega d t

private theorem source_Y_factor (o : Fin 759) (e : Fin 64) (d : Fin 2048)
    (i : Fin 24) (t : SpinIndex) :
    spinOperator (griessShortQ (Sum.inr (Sum.inl (o,e)))) (trialityYSpin d i) t =
      qSign (spinDot (sourceWordTheta (golayOctadLabel o)) t) *
      qSign (spinDot (golaySyndrome (integerParity (griessOctadNegativeInteger o e))) t) *
      qSign (griessOctadOmegaCoefficient e) * trialityYSpin d i (t + octadSpinCode o) := by
  rw [spinOperator_griessOctad, spinDot_add_left, qSign_add]
  rw [← add_assoc t (golayLabelCoefficients (golayOctadLabel o)), source_Y_omega]
  unfold octadSpinCode
  ring
private theorem source_Z_factor (o : Fin 759) (e : Fin 64) (d : Fin 2048)
    (t : SpinIndex) :
    spinOperator (griessShortQ (Sum.inr (Sum.inl (o,e)))) (trialityZSpin d) t =
      qSign (spinDot (sourceWordTheta (golayOctadLabel o)) t) *
      qSign (spinDot (golaySyndrome (integerParity (griessOctadNegativeInteger o e))) t) *
        trialityZSpin d (t + octadSpinCode o) := by
  rw [spinOperator_griessOctad, spinDot_add_left, qSign_add]
  rw [← add_assoc t (golayLabelCoefficients (golayOctadLabel o)), source_Z_omega]
  rfl

private theorem source_Y_contract (a b c d e f g : ℝ) :
    a*b*c*(d*e*f/Real.sqrt 2)*(g/Real.sqrt 2) = a*d*e*g*f/2*c*b := by
  calc
    _ = (a*b*c*d*e*f*g)/(Real.sqrt 2 * Real.sqrt 2) := by ring
    _ = _ := by rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
private theorem source_Z_contract (a b d f g : ℝ) :
    a*b*(d*f/Real.sqrt 2)*(g/Real.sqrt 2) = a*d*g*f/2*b := by
  simpa only [mul_one, one_mul] using source_Y_contract a b 1 d 1 f g

set_option backward.isDefEq.respectTransparency false in
theorem octadYSpin_pairing_normalform (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24) :
    spinOperator (griessShortQ (Sum.inr (Sum.inl (o,e)))) (trialityYSpin d i)
      (octadSpinLow f) * trialityYSpin f j (octadSpinLow f) =
      octadYSpinConstant o d f i j / 2 * qSign (griessOctadOmegaCoefficient e) *
        octadNegativeCharacter o e f := by
  rw [source_Y_factor]
  have hf : spinDictionaryCode (octadSpinLow f) = f := spinDictionaryCode_low f
  have hl : octadSpinLow f 11 = 0 := golayLabel_low_last f
  simp only [trialityYSpin, hf, hl, ite_true, qSign_zero, one_mul, mul_one]
  unfold octadYSpinConstant octadNegativeCharacter octadSpinSelector
  exact source_Y_contract _ _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem octadZSpin_pairing_normalform (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) :
    spinOperator (griessShortQ (Sum.inr (Sum.inl (o,e)))) (trialityZSpin d)
      (octadSpinLow f) * trialityZSpin f (octadSpinLow f) =
      octadZSpinConstant o d f / 2 * octadNegativeCharacter o e f := by
  rw [source_Z_factor]
  have hf : spinDictionaryCode (octadSpinLow f) = f := spinDictionaryCode_low f
  simp only [trialityZSpin, hf, ite_true, mul_one]
  unfold octadZSpinConstant octadNegativeCharacter octadSpinSelector
  exact source_Z_contract _ _ _ _ _

/-- Physical octad coordinates, divided by their absolute value2: signs on the
support and zero outside it. -/
noncomputable def octadPhysicalSign (o : Fin 759) (e : Fin 64) (i : Fin 24) : ℝ :=
  (griessShortIntegral (Sum.inr (Sum.inl (o,e))) i : ℝ) / 2

@[simp] theorem octadPhysicalSign_local (o : Fin 759) (e : Fin 64) (k : Fin 8) :
    octadPhysicalSign o e (golayOctadCoordinate o k) =
      if (trialityEvenMask e).testBit k.val then -1 else 1 := by
  rw [octadPhysicalSign, griessOctad_integral_local]
  split_ifs <;> norm_num

theorem octadPhysicalSign_outside (o : Fin 759) (e : Fin 64) (i : Fin 24)
    (hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val ≠ true) :
    octadPhysicalSign o e i = 0 := by
  rw [octadPhysicalSign, griessOctad_integral_zero o e i hi]
  norm_num

private theorem source_octad_scale (x y : ℝ) :
    2*(x/Real.sqrt 8)*(y/Real.sqrt 8) = (x/2)*(y/2) := by
  calc
    _ = 2*x*y/(Real.sqrt 8 * Real.sqrt 8) := by ring
    _ = _ := by rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)]; ring

/-- The actual octad tensor coefficient is the signed-coordinate matrix.
The diagonal term also covers tensor columns outside the octad support. -/
theorem conwayTensorCoefficient_octad_sign (o : Fin 759) (e : Fin 64) (i j : Fin 24) :
    conwayTensorCoefficient (Sum.inr (Sum.inl (o,e))) i j =
      (if i=j then 1 else 0) - octadPhysicalSign o e i * octadPhysicalSign o e j := by
  unfold conwayTensorCoefficient griessShortVector octadPhysicalSign
  rw [source_octad_scale]

set_option backward.isDefEq.respectTransparency false in
/-- Complete OYY source normalform with every octad-sign-dependent factor explicit. -/
theorem trialityOctadXYZ_cubic_YY_normalform (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 1 (finProdFinEquiv (d,i))))
        (trialityXYZBasis 1 (finProdFinEquiv (f,j))) =
      octadYSpinConstant o d f i j / 8 * qSign (griessOctadOmegaCoefficient e) *
        octadNegativeCharacter o e f *
          ((if i=j then 1 else 0) - octadPhysicalSign o e i * octadPhysicalSign o e j) := by
  rw [trialityOctadXYZ_cubic_YY_one_spin]
  change conwayTensorCoefficient (Sum.inr (Sum.inl (o,e))) i j / 4 *
    (spinOperator (griessShortQ (Sum.inr (Sum.inl (o,e)))) (trialityYSpin d i)
      (octadSpinLow f) * trialityYSpin f j (octadSpinLow f)) = _
  rw [octadYSpin_pairing_normalform, conwayTensorCoefficient_octad_sign]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Complete OZZ normalform; its source spin factor has no all-one correction sign. -/
theorem trialityOctadXYZ_cubic_ZZ_normalform (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 2 (finProdFinEquiv (d,i))))
        (trialityXYZBasis 2 (finProdFinEquiv (f,j))) =
      octadZSpinConstant o d f / 8 * octadNegativeCharacter o e f *
        ((if i=j then 1 else 0) - octadPhysicalSign o e i * octadPhysicalSign o e j) := by
  rw [trialityOctadXYZ_cubic_ZZ_one_spin]
  change conwayTensorCoefficient (Sum.inr (Sum.inl (o,e))) i j / 4 *
    (spinOperator (griessShortQ (Sum.inr (Sum.inl (o,e)))) (trialityZSpin d)
      (octadSpinLow f) * trialityZSpin f (octadSpinLow f)) = _
  rw [octadZSpin_pairing_normalform, conwayTensorCoefficient_octad_sign]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
