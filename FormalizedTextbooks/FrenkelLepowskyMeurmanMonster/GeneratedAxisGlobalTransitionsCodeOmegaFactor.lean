/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignCodeReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddTheta
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCrossPhase

/-! The actual all-one factor of every source code, with all quarter-weight phases retained. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original low source label of an arbitrary eleven-bit code. -/
def generatedAxisGlobalCodeLowLabel (a : Fin 2048) : Fin 4096 := ⟨a.val, by omega⟩

/-- The actual full source label after adding the all-one code. -/
def generatedAxisGlobalCodeHighLabel (a : Fin 2048) : Fin 4096 :=
  ⟨a.val + 2048, by omega⟩

/-- The two displayed labels have exactly their actual all-one coordinate difference. -/
theorem generatedAxisGlobalCodeHighLabel_coeff (a : Fin 2048) :
    golayLabelCoefficients (generatedAxisGlobalCodeHighLabel a) =
      golayLabelCoefficients (generatedAxisGlobalCodeLowLabel a) + Pi.single 11 1 :=
  (golayLabel_low_add_omega a).symm

/-- All-one addition preserves the actual theta polynomial on arbitrary source labels. -/
theorem generatedAxisGlobalCodeHigh_theta (a : Fin 2048) :
    sourceCodeThetaPolynomial (golayLabelCoefficients (generatedAxisGlobalCodeHighLabel a)) =
      sourceCodeThetaPolynomial (golayLabelCoefficients (generatedAxisGlobalCodeLowLabel a)) := by
  rw [generatedAxisGlobalCodeHighLabel_coeff, sourceCodeThetaPolynomial_add_omega]

/-- The actual quarter-weight character is unchanged by the all-one code. -/
theorem generatedAxisGlobalCodeHigh_quarter (a : Fin 2048) :
    ((golayMaskWeight (golayEncodedMask (generatedAxisGlobalCodeHighLabel a).val) / 4 : ℕ) :
      ZMod 2) =
      (golayMaskWeight (golayEncodedMask (generatedAxisGlobalCodeLowLabel a).val) / 4 : ℕ) := by
  rw [← sourceCodeThetaPolynomial_self_dot, generatedAxisGlobalCodeHigh_theta,
    generatedAxisGlobalCodeHighLabel_coeff, spinDot_add_right]
  have h : spinDot
      (sourceCodeThetaPolynomial (golayLabelCoefficients (generatedAxisGlobalCodeLowLabel a)))
      (Pi.single 11 1) = 0 := by
    rw [← sourceWordTheta_polynomial]
    exact sourceWordTheta_dot_omega _
  rw [h, add_zero, sourceCodeThetaPolynomial_self_dot]

/-- Every high source lift factors by genuine Omega with its exact arbitrary central sign. -/
theorem generatedAxisGlobalCodeHigh_factor (a : Fin 2048) (ε : ZMod 2) :
    sourceQCode (generatedAxisGlobalCodeHighLabel a) ε =
      sourceOmegaQ * sourceQCode (generatedAxisGlobalCodeLowLabel a) ε := by
  apply spinRepresentation_injective
  rw [map_mul]
  apply LinearEquiv.ext
  intro x
  funext t
  rw [LinearEquiv.mul_apply, sourceOmegaQ_spin]
  change qSign (spinPhase (sourceQCode (generatedAxisGlobalCodeHighLabel a) ε) t) *
    x (t + spinTranslation (sourceQCode (generatedAxisGlobalCodeHighLabel a) ε)) =
      qSign (spinPhase (sourceQCode (generatedAxisGlobalCodeLowLabel a) ε) (t + Pi.single 11 1)) *
        x ((t + Pi.single 11 1) +
          spinTranslation (sourceQCode (generatedAxisGlobalCodeLowLabel a) ε))
  rw [spinPhase, spinPhase, sourceQCode_translation, sourceQCode_translation,
    sourceQCode_modulation, sourceQCode_modulation, generatedAxisGlobalCodeHigh_theta,
    generatedAxisGlobalCodeHighLabel_coeff, spinDot_add_right]
  have h : spinDot
      (sourceCodeThetaPolynomial (golayLabelCoefficients (generatedAxisGlobalCodeLowLabel a)))
      (Pi.single 11 1) = 0 := by
    rw [← sourceWordTheta_polynomial]
    exact sourceWordTheta_dot_omega _
  rw [h, add_zero]
  change qSign (ε + (golayMaskWeight
      (golayEncodedMask (generatedAxisGlobalCodeHighLabel a).val) / 4 : ℕ) + _) * _ =
    qSign (ε + (golayMaskWeight
      (golayEncodedMask (generatedAxisGlobalCodeLowLabel a).val) / 4 : ℕ) + _) * _
  rw [generatedAxisGlobalCodeHigh_quarter]
  congr 2
  abel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
