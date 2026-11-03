/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.HahnSeries.DiagonalLaurent
import Mathlib.Data.ZMod.Basic

open LaurentPolynomial

namespace HahnSeries

private theorem sourceDiag_bddBelow {R : Type*} [CommSemiring R]
    (d : ℤ) (c : ℤ → R) (j₀ : ℤ) :
    BddBelow (Function.support fun j : ℤ =>
      if j₀ ≤ j then
        (LaurentPolynomial.C (c j) * LaurentPolynomial.T (d - j) : LaurentPolynomial R)
      else 0) :=
  ⟨j₀, fun j hj => by
    by_contra h
    simp [h] at hj⟩

private noncomputable def sourceDiag {R : Type*} [CommSemiring R]
    (d : ℤ) (c : ℤ → R) (j₀ : ℤ) : HahnSeries ℤ (LaurentPolynomial R) :=
  ofSuppBddBelow
    (fun j => if j₀ ≤ j then LaurentPolynomial.C (c j) * LaurentPolynomial.T (d - j)
      else 0)
    (sourceDiag_bddBelow d c j₀)

private theorem sourceDiag_eq {R : Type*} [CommSemiring R]
    (d : ℤ) (c : ℤ → R) (j₀ : ℤ) :
    sourceDiag d c j₀ = diagonalLaurentSeries d c j₀ := by
  apply HahnSeries.ext
  funext y
  unfold sourceDiag
  rw [coeff_ofSuppBddBelow, coeff_diagonalLaurentSeries]
  by_cases h : j₀ ≤ y
  · simpa only [h, ↓reduceIte] using (single_eq_C_mul_T (c y) (d - y)).symm
  · simp [h]

private noncomputable def sourceEps {R : Type*} [CommRing R] :
    HahnSeries ℤ (LaurentPolynomial R) := sourceDiag (-1) (fun _ => 1) 0

example : sourceEps (R := ℚ) =
    (↑((variableDifferenceUnit (R := ℚ))⁻¹) : HahnSeries ℤ (LaurentPolynomial ℚ)) := by
  rw [sourceEps, sourceDiag_eq, coe_inv_variableDifferenceUnit]

private def diagonalCoeffs (j : ℤ) : ℤ :=
  if j = -2 then 7 else if j = 1 then -4 else if j = -3 then 11 else 0

private noncomputable def integerDiagonal : HahnSeries ℤ (LaurentPolynomial ℤ) :=
  diagonalLaurentSeries 3 diagonalCoeffs (-2)

example : (integerDiagonal.coeff (-2)).coeff 5 = 7 := by
  rw [integerDiagonal, coeff_coeff_diagonalLaurentSeries]
  norm_num [diagonalCoeffs]

example : (integerDiagonal.coeff 1).coeff 2 = -4 := by
  rw [integerDiagonal, coeff_coeff_diagonalLaurentSeries]
  norm_num [diagonalCoeffs]

-- The sequence value below the cutoff is deliberately nonzero, but the series coefficient is zero.
example : (integerDiagonal.coeff (-3)).coeff 6 = 0 := by
  rw [integerDiagonal, coeff_coeff_diagonalLaurentSeries]
  norm_num

example : (integerDiagonal.coeff (-2)).coeff 0 = 0 := by
  rw [integerDiagonal, coeff_coeff_diagonalLaurentSeries]
  norm_num

example : (integerDiagonal.coeff 1).coeff 5 = 0 := by
  rw [integerDiagonal, coeff_coeff_diagonalLaurentSeries]
  norm_num

private noncomputable def inverseInt : HahnSeries ℤ (LaurentPolynomial ℤ) :=
  ↑((variableDifferenceUnit (R := ℤ))⁻¹)

example : (inverseInt.coeff 0).coeff (-1) = 1 := by
  rw [inverseInt, coe_inv_variableDifferenceUnit, coeff_coeff_diagonalLaurentSeries]
  norm_num

example : (inverseInt.coeff 1).coeff (-2) = 1 := by
  rw [inverseInt, coe_inv_variableDifferenceUnit, coeff_coeff_diagonalLaurentSeries]
  norm_num

example : (inverseInt.coeff 2).coeff (-3) = 1 := by
  rw [inverseInt, coe_inv_variableDifferenceUnit, coeff_coeff_diagonalLaurentSeries]
  norm_num

private noncomputable def swappedCoeff (f : HahnSeries ℤ (LaurentPolynomial ℤ))
    (x y : ℤ) : ℤ := (f.coeff x).coeff y

-- Reading the outer and inner exponents in the opposite order recovers the source's second view.
example : swappedCoeff inverseInt 1 (-2) = 1 := by
  rw [swappedCoeff, inverseInt, coe_inv_variableDifferenceUnit,
    coeff_coeff_diagonalLaurentSeries]
  norm_num

example :
    (single 0 (T 1) - single 1 1) * inverseInt =
      (1 : HahnSeries ℤ (LaurentPolynomial ℤ)) := by
  unfold inverseInt
  rw [← coe_variableDifferenceUnit]
  exact (variableDifferenceUnit (R := ℤ)).val_inv

example :
    ((((↑((variableDifferenceUnit (R := ℚ))⁻¹) :
      HahnSeries ℤ (LaurentPolynomial ℚ)) ^ 2).coeff 1).coeff (-3)) = 2 := by
  change ((((↑((variableDifferenceUnit (R := ℚ))⁻¹) :
    HahnSeries ℤ (LaurentPolynomial ℚ)) ^ (1 + 1)).coeff 1).coeff (-3)) = 2
  rw [coe_inv_variableDifferenceUnit_pow_succ, coeff_coeff_diagonalLaurentSeries]
  norm_num

example :
    ((((↑((variableDifferenceUnit (R := ℚ))⁻¹) :
      HahnSeries ℤ (LaurentPolynomial ℚ)) ^ 2).coeff 2).coeff (-4)) = 3 := by
  change ((((↑((variableDifferenceUnit (R := ℚ))⁻¹) :
    HahnSeries ℤ (LaurentPolynomial ℚ)) ^ (1 + 1)).coeff 2).coeff (-4)) = 3
  rw [coe_inv_variableDifferenceUnit_pow_succ, coeff_coeff_diagonalLaurentSeries]
  norm_num

example :
    ((((↑((variableDifferenceUnit (R := ℚ))⁻¹) :
      HahnSeries ℤ (LaurentPolynomial ℚ)) ^ 3).coeff 1).coeff (-4)) = 3 := by
  change ((((↑((variableDifferenceUnit (R := ℚ))⁻¹) :
    HahnSeries ℤ (LaurentPolynomial ℚ)) ^ (2 + 1)).coeff 1).coeff (-4)) = 3
  rw [coe_inv_variableDifferenceUnit_pow_succ, coeff_coeff_diagonalLaurentSeries]
  norm_num

example :
    ((((↑((variableDifferenceUnit (R := ℚ))⁻¹) :
      HahnSeries ℤ (LaurentPolynomial ℚ)) ^ 3).coeff 2).coeff (-5)) = 6 := by
  change ((((↑((variableDifferenceUnit (R := ℚ))⁻¹) :
    HahnSeries ℤ (LaurentPolynomial ℚ)) ^ (2 + 1)).coeff 2).coeff (-5)) = 6
  rw [coe_inv_variableDifferenceUnit_pow_succ, coeff_coeff_diagonalLaurentSeries]
  norm_num [Nat.choose]

example :
    ((((↑((variableDifferenceUnit (R := ℚ))⁻¹) :
      HahnSeries ℤ (LaurentPolynomial ℚ)) ^ 3).coeff (-1)).coeff (-2)) = 0 := by
  change ((((↑((variableDifferenceUnit (R := ℚ))⁻¹) :
    HahnSeries ℤ (LaurentPolynomial ℚ)) ^ (2 + 1)).coeff (-1)).coeff (-2)) = 0
  rw [coe_inv_variableDifferenceUnit_pow_succ, coeff_coeff_diagonalLaurentSeries]
  norm_num

-- The coefficient `choose 2 1` vanishes after casting to characteristic two.
example :
    ((((↑((variableDifferenceUnit (R := ZMod 2))⁻¹) :
      HahnSeries ℤ (LaurentPolynomial (ZMod 2))) ^ 2).coeff 1).coeff (-3)) = 0 := by
  change ((((↑((variableDifferenceUnit (R := ZMod 2))⁻¹) :
    HahnSeries ℤ (LaurentPolynomial (ZMod 2))) ^ (1 + 1)).coeff 1).coeff (-3)) = 0
  rw [coe_inv_variableDifferenceUnit_pow_succ, coeff_coeff_diagonalLaurentSeries]
  decide

example :
    ((((↑((variableDifferenceUnit (R := ZMod 2))⁻¹) :
      HahnSeries ℤ (LaurentPolynomial (ZMod 2))) ^ 2).coeff 2).coeff (-4)) = 1 := by
  change ((((↑((variableDifferenceUnit (R := ZMod 2))⁻¹) :
    HahnSeries ℤ (LaurentPolynomial (ZMod 2))) ^ (1 + 1)).coeff 2).coeff (-4)) = 1
  rw [coe_inv_variableDifferenceUnit_pow_succ, coeff_coeff_diagonalLaurentSeries]
  decide

#print axioms diagonalLaurentSeries
#print axioms coeff_diagonalLaurentSeries
#print axioms coeff_coeff_diagonalLaurentSeries
#print axioms coeff_coeff_variableDifference_mul
#print axioms variableDifferenceUnit
#print axioms coe_variableDifferenceUnit
#print axioms coe_inv_variableDifferenceUnit
#print axioms coe_inv_variableDifferenceUnit_pow_succ

end HahnSeries
