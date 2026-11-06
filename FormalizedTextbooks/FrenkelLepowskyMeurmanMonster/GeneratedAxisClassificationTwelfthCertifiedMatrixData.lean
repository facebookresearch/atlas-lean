/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData11

/-! Complete actual physical candidate matrices and their integral basis certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- All twelve complete integer coordinate matrices. -/
def generatedTwelfthCertifiedNumerator : Fin 12 → Matrix (Fin 24) (Fin 24) ℤ :=
  ![generatedTwelfthCertifiedNumerator00,
    generatedTwelfthCertifiedNumerator01,
    generatedTwelfthCertifiedNumerator02,
    generatedTwelfthCertifiedNumerator03,
    generatedTwelfthCertifiedNumerator04,
    generatedTwelfthCertifiedNumerator05,
    generatedTwelfthCertifiedNumerator06,
    generatedTwelfthCertifiedNumerator07,
    generatedTwelfthCertifiedNumerator08,
    generatedTwelfthCertifiedNumerator09,
    generatedTwelfthCertifiedNumerator10,
    generatedTwelfthCertifiedNumerator11]

/-- All twelve complete integer coordinate matrices. -/
def generatedTwelfthCertifiedIntegral : Fin 12 → Matrix (Fin 24) (Fin 24) ℤ :=
  ![generatedTwelfthCertifiedIntegral00,
    generatedTwelfthCertifiedIntegral01,
    generatedTwelfthCertifiedIntegral02,
    generatedTwelfthCertifiedIntegral03,
    generatedTwelfthCertifiedIntegral04,
    generatedTwelfthCertifiedIntegral05,
    generatedTwelfthCertifiedIntegral06,
    generatedTwelfthCertifiedIntegral07,
    generatedTwelfthCertifiedIntegral08,
    generatedTwelfthCertifiedIntegral09,
    generatedTwelfthCertifiedIntegral10,
    generatedTwelfthCertifiedIntegral11]

/-- All twelve complete integer coordinate matrices. -/
def generatedTwelfthCertifiedIntegralInverse : Fin 12 → Matrix (Fin 24) (Fin 24) ℤ :=
  ![generatedTwelfthCertifiedIntegralInverse00,
    generatedTwelfthCertifiedIntegralInverse01,
    generatedTwelfthCertifiedIntegralInverse02,
    generatedTwelfthCertifiedIntegralInverse03,
    generatedTwelfthCertifiedIntegralInverse04,
    generatedTwelfthCertifiedIntegralInverse05,
    generatedTwelfthCertifiedIntegralInverse06,
    generatedTwelfthCertifiedIntegralInverse07,
    generatedTwelfthCertifiedIntegralInverse08,
    generatedTwelfthCertifiedIntegralInverse09,
    generatedTwelfthCertifiedIntegralInverse10,
    generatedTwelfthCertifiedIntegralInverse11]

/-- Actual positive spatial denominators of every complete compact lift. -/
def generatedTwelfthCertifiedDenominator : Fin 12 → ℕ :=
  ![1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- Every displayed whole spatial denominator is nonzero. -/
theorem generatedTwelfth_certified_denominator_ne_zero (g : Fin 12) :
    generatedTwelfthCertifiedDenominator g ≠ 0 := by
  fin_cases g <;> decide

/-- All twelve whole orthogonal left identities are checked. -/
theorem generatedTwelfth_certified_orthogonal_left (g : Fin 12) :
    (generatedTwelfthCertifiedNumerator g).transpose *
      generatedTwelfthCertifiedNumerator g =
        (generatedTwelfthCertifiedDenominator g *
          generatedTwelfthCertifiedDenominator g : ℤ) • 1 := by
  fin_cases g
  · exact generatedTwelfth_certified_matrix_00_orthogonal_left
  · exact generatedTwelfth_certified_matrix_01_orthogonal_left
  · exact generatedTwelfth_certified_matrix_02_orthogonal_left
  · exact generatedTwelfth_certified_matrix_03_orthogonal_left
  · exact generatedTwelfth_certified_matrix_04_orthogonal_left
  · exact generatedTwelfth_certified_matrix_05_orthogonal_left
  · exact generatedTwelfth_certified_matrix_06_orthogonal_left
  · exact generatedTwelfth_certified_matrix_07_orthogonal_left
  · exact generatedTwelfth_certified_matrix_08_orthogonal_left
  · exact generatedTwelfth_certified_matrix_09_orthogonal_left
  · exact generatedTwelfth_certified_matrix_10_orthogonal_left
  · exact generatedTwelfth_certified_matrix_11_orthogonal_left

/-- All twelve whole orthogonal right identities are checked. -/
theorem generatedTwelfth_certified_orthogonal_right (g : Fin 12) :
    generatedTwelfthCertifiedNumerator g *
      (generatedTwelfthCertifiedNumerator g).transpose =
        (generatedTwelfthCertifiedDenominator g *
          generatedTwelfthCertifiedDenominator g : ℤ) • 1 := by
  fin_cases g
  · exact generatedTwelfth_certified_matrix_00_orthogonal_right
  · exact generatedTwelfth_certified_matrix_01_orthogonal_right
  · exact generatedTwelfth_certified_matrix_02_orthogonal_right
  · exact generatedTwelfth_certified_matrix_03_orthogonal_right
  · exact generatedTwelfth_certified_matrix_04_orthogonal_right
  · exact generatedTwelfth_certified_matrix_05_orthogonal_right
  · exact generatedTwelfth_certified_matrix_06_orthogonal_right
  · exact generatedTwelfth_certified_matrix_07_orthogonal_right
  · exact generatedTwelfth_certified_matrix_08_orthogonal_right
  · exact generatedTwelfth_certified_matrix_09_orthogonal_right
  · exact generatedTwelfth_certified_matrix_10_orthogonal_right
  · exact generatedTwelfth_certified_matrix_11_orthogonal_right

/-- All twelve whole basis identities are checked. -/
theorem generatedTwelfth_certified_basis (g : Fin 12) :
    generatedTwelfthCertifiedNumerator g * leechBasisMatrix =
      (generatedTwelfthCertifiedDenominator g : ℤ) •
        (leechBasisMatrix * generatedTwelfthCertifiedIntegral g) := by
  fin_cases g
  · exact generatedTwelfth_certified_matrix_00_basis
  · exact generatedTwelfth_certified_matrix_01_basis
  · exact generatedTwelfth_certified_matrix_02_basis
  · exact generatedTwelfth_certified_matrix_03_basis
  · exact generatedTwelfth_certified_matrix_04_basis
  · exact generatedTwelfth_certified_matrix_05_basis
  · exact generatedTwelfth_certified_matrix_06_basis
  · exact generatedTwelfth_certified_matrix_07_basis
  · exact generatedTwelfth_certified_matrix_08_basis
  · exact generatedTwelfth_certified_matrix_09_basis
  · exact generatedTwelfth_certified_matrix_10_basis
  · exact generatedTwelfth_certified_matrix_11_basis

/-- All twelve whole integral inverse identities are checked. -/
theorem generatedTwelfth_certified_integral_inverse (g : Fin 12) :
    generatedTwelfthCertifiedIntegral g * generatedTwelfthCertifiedIntegralInverse g = 1 := by
  fin_cases g
  · exact generatedTwelfth_certified_matrix_00_integral_inverse
  · exact generatedTwelfth_certified_matrix_01_integral_inverse
  · exact generatedTwelfth_certified_matrix_02_integral_inverse
  · exact generatedTwelfth_certified_matrix_03_integral_inverse
  · exact generatedTwelfth_certified_matrix_04_integral_inverse
  · exact generatedTwelfth_certified_matrix_05_integral_inverse
  · exact generatedTwelfth_certified_matrix_06_integral_inverse
  · exact generatedTwelfth_certified_matrix_07_integral_inverse
  · exact generatedTwelfth_certified_matrix_08_integral_inverse
  · exact generatedTwelfth_certified_matrix_09_integral_inverse
  · exact generatedTwelfth_certified_matrix_10_integral_inverse
  · exact generatedTwelfth_certified_matrix_11_integral_inverse

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
