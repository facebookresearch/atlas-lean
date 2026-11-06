/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometryData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometryData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometryData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometryData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometryData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometryData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometryData06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometryData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometryData08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometryData09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometryData10

/-! Whole rational isometry certificates for all eleven genuine lattice candidates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- All eleven complete integral lattice inverses in their original coordinate basis. -/
def generatedNinthLowerSpinDirectIntegralInverse : Fin 11 → Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    generatedNinthLowerSpinDirectIntegralInverse00,
    generatedNinthLowerSpinDirectIntegralInverse01,
    generatedNinthLowerSpinDirectIntegralInverse02,
    generatedNinthLowerSpinDirectIntegralInverse03,
    generatedNinthLowerSpinDirectIntegralInverse04,
    generatedNinthLowerSpinDirectIntegralInverse05,
    generatedNinthLowerSpinDirectIntegralInverse06,
    generatedNinthLowerSpinDirectIntegralInverse07,
    generatedNinthLowerSpinDirectIntegralInverse08,
    generatedNinthLowerSpinDirectIntegralInverse09,
    generatedNinthLowerSpinDirectIntegralInverse10
  ]

/-- Every complete rational candidate has both required orthogonality identities. -/
theorem generatedNinth_lower_spin_direct_isometry_left (i : Fin 11) :
    (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator i)).transpose *
      Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator i) =
      ((generatedNinthLowerSpinTensorSpatialDenominator i : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator i : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  fin_cases i
  · exact generatedNinth_lower_spin_direct_isometry_left_00
  · exact generatedNinth_lower_spin_direct_isometry_left_01
  · exact generatedNinth_lower_spin_direct_isometry_left_02
  · exact generatedNinth_lower_spin_direct_isometry_left_03
  · exact generatedNinth_lower_spin_direct_isometry_left_04
  · exact generatedNinth_lower_spin_direct_isometry_left_05
  · exact generatedNinth_lower_spin_direct_isometry_left_06
  · exact generatedNinth_lower_spin_direct_isometry_left_07
  · exact generatedNinth_lower_spin_direct_isometry_left_08
  · exact generatedNinth_lower_spin_direct_isometry_left_09
  · exact generatedNinth_lower_spin_direct_isometry_left_10

/-- Every complete rational candidate has both required orthogonality identities. -/
theorem generatedNinth_lower_spin_direct_isometry_right (i : Fin 11) :
    Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator i) *
      (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator i)).transpose =
      ((generatedNinthLowerSpinTensorSpatialDenominator i : ℤ) *
        (generatedNinthLowerSpinTensorSpatialDenominator i : ℤ)) •
          (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  fin_cases i
  · exact generatedNinth_lower_spin_direct_isometry_right_00
  · exact generatedNinth_lower_spin_direct_isometry_right_01
  · exact generatedNinth_lower_spin_direct_isometry_right_02
  · exact generatedNinth_lower_spin_direct_isometry_right_03
  · exact generatedNinth_lower_spin_direct_isometry_right_04
  · exact generatedNinth_lower_spin_direct_isometry_right_05
  · exact generatedNinth_lower_spin_direct_isometry_right_06
  · exact generatedNinth_lower_spin_direct_isometry_right_07
  · exact generatedNinth_lower_spin_direct_isometry_right_08
  · exact generatedNinth_lower_spin_direct_isometry_right_09
  · exact generatedNinth_lower_spin_direct_isometry_right_10

/-- Every complete integral coordinate action has its exact integral inverse. -/
theorem generatedNinth_lower_spin_direct_isometry_inverse (i : Fin 11) :
    generatedNinthLowerSpinDirectIntegralMatrix i *
      generatedNinthLowerSpinDirectIntegralInverse i = 1 := by
  fin_cases i
  · exact generatedNinth_lower_spin_direct_isometry_inverse_00
  · exact generatedNinth_lower_spin_direct_isometry_inverse_01
  · exact generatedNinth_lower_spin_direct_isometry_inverse_02
  · exact generatedNinth_lower_spin_direct_isometry_inverse_03
  · exact generatedNinth_lower_spin_direct_isometry_inverse_04
  · exact generatedNinth_lower_spin_direct_isometry_inverse_05
  · exact generatedNinth_lower_spin_direct_isometry_inverse_06
  · exact generatedNinth_lower_spin_direct_isometry_inverse_07
  · exact generatedNinth_lower_spin_direct_isometry_inverse_08
  · exact generatedNinth_lower_spin_direct_isometry_inverse_09
  · exact generatedNinth_lower_spin_direct_isometry_inverse_10

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
