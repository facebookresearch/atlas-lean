/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagMatrix

/-! Two intrinsic spatial supports recovered from the actual seventh matrix by polynomials. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The three physical coordinates carrying the genuine short-root triangle. -/
def generatedSeventhTriangle (i : Fin 24) : Prop := i = 16 ∨ i = 17 ∨ i = 19

/-- The five diagonal coordinates with the larger original matrix value. -/
def generatedSeventhFive (i : Fin 24) : Prop :=
  i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 18

instance (i : Fin 24) : Decidable (generatedSeventhTriangle i) := inferInstanceAs
  (Decidable (i = 16 ∨ i = 17 ∨ i = 19))
instance (i : Fin 24) : Decidable (generatedSeventhFive i) := inferInstanceAs
  (Decidable (i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 18))

/-- Three times the orthogonal projection onto the actual two-root triangle plane. -/
def generatedSeventhPlaneNumerator : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  if generatedSeventhTriangle i ∧ generatedSeventhTriangle j then
    if i = j then 2 else -1
  else 0

/-- Three times the orthogonal projection onto the actual six-dimensional larger support. -/
def generatedSeventhSixNumerator : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  if i = j ∧ generatedSeventhFive i then 3
  else if generatedSeventhTriangle i ∧ generatedSeventhTriangle j then 1 else 0

/-- An integral denominator-clearing of the actual matrix. -/
def generatedSeventhMatrixNumerator : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  if i = j then if generatedSeventhFive i then 17 else 9
  else if generatedSeventhTriangle i ∧ generatedSeventhTriangle j then 4 else 0

/-- The centered polynomial isolates the actual two-dimensional support. -/
theorem generatedSeventh_plane_polynomial_integer :
    generatedSeventhMatrixNumerator * generatedSeventhMatrixNumerator -
      (26 : ℤ) • generatedSeventhMatrixNumerator + (153 : ℤ) • 1 =
      (16 : ℤ) • generatedSeventhPlaneNumerator := by
  decide +kernel

/-- A second centered polynomial isolates the actual six-dimensional support. -/
theorem generatedSeventh_six_polynomial_integer :
    generatedSeventhMatrixNumerator * generatedSeventhMatrixNumerator -
      (14 : ℤ) • generatedSeventhMatrixNumerator + (45 : ℤ) • 1 =
      (32 : ℤ) • generatedSeventhSixNumerator := by
  decide +kernel

/-- The two actual supports reconstruct every coordinate of the matrix. -/
theorem generatedSeventh_support_reconstruction_integer :
    (3 : ℤ) • generatedSeventhMatrixNumerator =
      (27 : ℤ) • 1 + (8 : ℤ) • generatedSeventhSixNumerator -
        (4 : ℤ) • generatedSeventhPlaneNumerator := by
  decide +kernel

/-- The actual real two-root support matrix, with scalar three retained. -/
def generatedSeventhPlaneSupport : Matrix (Fin 24) (Fin 24) ℝ :=
  generatedSeventhPlaneNumerator.map (Int.castRingHom ℝ)

/-- The actual real six-dimensional support matrix, with scalar three retained. -/
def generatedSeventhSixSupport : Matrix (Fin 24) (Fin 24) ℝ :=
  generatedSeventhSixNumerator.map (Int.castRingHom ℝ)

/-- The denominator-cleared actual real matrix. -/
def generatedSeventhMatrixIntegerReal : Matrix (Fin 24) (Fin 24) ℝ :=
  generatedSeventhMatrixNumerator.map (Int.castRingHom ℝ)

/-- The literal full-axis matrix equals its original integer numerator divided by thirty-two. -/
theorem generatedSeventh_matrix_numerator_real :
    generatedSeventhAxisMatrix = (1 / 32 : ℝ) • generatedSeventhMatrixIntegerReal := by
  ext i j
  change generatedSeventhAxisMatrix i j =
    (1 / 32 : ℝ) * (generatedSeventhMatrixNumerator i j : ℝ)
  simp only [generatedSeventhAxisMatrix, generatedSeventhMiddlePairValue,
    generatedSeventhMatrixNumerator, generatedSeventhFive, generatedSeventhTriangle]
  split_ifs <;> norm_num <;> omega

/-- The two-root support is an actual polynomial of the real matrix numerator. -/
theorem generatedSeventh_plane_polynomial_real :
    generatedSeventhMatrixIntegerReal * generatedSeventhMatrixIntegerReal -
      (26 : ℝ) • generatedSeventhMatrixIntegerReal + (153 : ℝ) • 1 =
      (16 : ℝ) • generatedSeventhPlaneSupport := by
  ext i j
  have h := congrFun (congrFun generatedSeventh_plane_polynomial_integer i) j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
    smul_eq_mul,
    Matrix.one_apply] at h
  change (∑ k, (generatedSeventhMatrixNumerator i k : ℝ) *
      (generatedSeventhMatrixNumerator k j : ℝ)) - 26 *
      (generatedSeventhMatrixNumerator i j : ℝ) + 153 * (if i = j then 1 else 0) =
      16 * (generatedSeventhPlaneNumerator i j : ℝ)
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- The larger support is a second actual polynomial of the real matrix numerator. -/
theorem generatedSeventh_six_polynomial_real :
    generatedSeventhMatrixIntegerReal * generatedSeventhMatrixIntegerReal -
      (14 : ℝ) • generatedSeventhMatrixIntegerReal + (45 : ℝ) • 1 =
      (32 : ℝ) • generatedSeventhSixSupport := by
  ext i j
  have h := congrFun (congrFun generatedSeventh_six_polynomial_integer i) j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
    smul_eq_mul,
    Matrix.one_apply] at h
  change (∑ k, (generatedSeventhMatrixNumerator i k : ℝ) *
      (generatedSeventhMatrixNumerator k j : ℝ)) - 14 *
      (generatedSeventhMatrixNumerator i j : ℝ) + 45 * (if i = j then 1 else 0) =
      32 * (generatedSeventhSixNumerator i j : ℝ)
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- The real matrix is recovered from the two genuine support matrices. -/
theorem generatedSeventh_support_reconstruction_real :
    (3 : ℝ) • generatedSeventhMatrixIntegerReal =
      (27 : ℝ) • 1 + (8 : ℝ) • generatedSeventhSixSupport -
        (4 : ℝ) • generatedSeventhPlaneSupport := by
  ext i j
  have h := congrFun (congrFun generatedSeventh_support_reconstruction_integer i) j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply] at h
  change 3 * (generatedSeventhMatrixNumerator i j : ℝ) =
    27 * (if i = j then 1 else 0) + 8 * (generatedSeventhSixNumerator i j : ℝ) -
      4 * (generatedSeventhPlaneNumerator i j : ℝ)
  split_ifs at h ⊢ <;> exact_mod_cast h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
