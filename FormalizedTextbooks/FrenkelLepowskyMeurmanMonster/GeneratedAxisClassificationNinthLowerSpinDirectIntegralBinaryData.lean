/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData10

/-! Complete integral-basis certificates for all eleven actual lower spatial numerators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The entire integral basis action matrix for each of the eleven literal spatial sources. -/
def generatedNinthLowerSpinDirectIntegralMatrix : Fin 11 → Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    generatedNinthLowerSpinDirectIntegralMatrix00,
    generatedNinthLowerSpinDirectIntegralMatrix01,
    generatedNinthLowerSpinDirectIntegralMatrix02,
    generatedNinthLowerSpinDirectIntegralMatrix03,
    generatedNinthLowerSpinDirectIntegralMatrix04,
    generatedNinthLowerSpinDirectIntegralMatrix05,
    generatedNinthLowerSpinDirectIntegralMatrix06,
    generatedNinthLowerSpinDirectIntegralMatrix07,
    generatedNinthLowerSpinDirectIntegralMatrix08,
    generatedNinthLowerSpinDirectIntegralMatrix09,
    generatedNinthLowerSpinDirectIntegralMatrix10
  ]

/-- All original numerator matrices satisfy the complete actual integral-basis identity. -/
theorem generatedNinth_lower_spin_direct_integral_basis (i : Fin 11) :
    Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator i) *
      leechBasisMatrix =
      (generatedNinthLowerSpinTensorSpatialDenominator i : ℤ) •
        (leechBasisMatrix * generatedNinthLowerSpinDirectIntegralMatrix i) := by
  fin_cases i
  · exact generatedNinth_lower_spin_direct_integral_basis_00
  · exact generatedNinth_lower_spin_direct_integral_basis_01
  · exact generatedNinth_lower_spin_direct_integral_basis_02
  · exact generatedNinth_lower_spin_direct_integral_basis_03
  · exact generatedNinth_lower_spin_direct_integral_basis_04
  · exact generatedNinth_lower_spin_direct_integral_basis_05
  · exact generatedNinth_lower_spin_direct_integral_basis_06
  · exact generatedNinth_lower_spin_direct_integral_basis_07
  · exact generatedNinth_lower_spin_direct_integral_basis_08
  · exact generatedNinth_lower_spin_direct_integral_basis_09
  · exact generatedNinth_lower_spin_direct_integral_basis_10

/-- Every literal spatial denominator is nonzero. -/
theorem generatedNinth_lower_spin_direct_integral_denominator (i : Fin 11) :
    generatedNinthLowerSpinTensorSpatialDenominator i ≠ 0 := by
  fin_cases i <;> decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
