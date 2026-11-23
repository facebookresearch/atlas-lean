/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.LinearCoeffList
public import Mathlib.Data.List.GetD
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

open Polynomial

namespace Polynomial

private def sourceMulStep (r c : ℤ) (l : List ℤ) : List ℤ :=
  (List.range (l.length + 1)).map fun j =>
    r * l.getD j 0 + c * (0 :: l).getD j 0

private theorem sourceMulStep_eq (r c : ℤ) (l : List ℤ) :
    sourceMulStep r c l = mulLinearCoeffList r c l := by
  apply List.ext_getElem
  · simp [sourceMulStep, length_mulLinearCoeffList]
  · intro j hjSource hjUpdate
    rw [← List.getD_eq_getElem _ 0 hjSource,
      ← List.getD_eq_getElem _ 0 hjUpdate, getD_mulLinearCoeffList]
    have hj : j < l.length + 1 := by
      simpa [sourceMulStep] using hjSource
    simp [sourceMulStep, hj]

/-- The original signed example, including its dense leading coefficient. -/
example : mulLinearCoeffList (2 : ℤ) 3 [-1, 4] = [-2, 5, 12] := by
  norm_num [mulLinearCoeffList]

/-- The list operation agrees with left multiplication of its little-endian polynomial. -/
example : ofCoeffList (mulLinearCoeffList (2 : ℤ) 3 [-1, 4]) =
    (C 2 + X * C 3) * ofCoeffList [-1, 4] :=
  ofCoeffList_mulLinearCoeffList 2 3 [-1, 4]

/-- Two distinct factors update the constant list `[1]` to the hand-computed quadratic. -/
example : mulLinearCoeffList (-1 : ℤ) 4 (mulLinearCoeffList 2 3 [1]) = [-2, 5, 12] := by
  norm_num [mulLinearCoeffList]

/-- The empty list still grows by one dense zero coefficient. -/
example : mulLinearCoeffList (7 : ℤ) 11 [] = [0] := by
  norm_num [mulLinearCoeffList]

/-- Zero factors preserve all dense positions and add one more. -/
example : mulLinearCoeffList (0 : ℤ) 0 [0, 0, 0] = [0, 0, 0, 0] := by
  norm_num [mulLinearCoeffList]

/-- A constant factor still grows the list when its linear coefficient is zero. -/
example : mulLinearCoeffList (3 : ℤ) 0 [2, -1] = [6, -3, 0] := by
  norm_num [mulLinearCoeffList]

/-- Signed cancellation occurs in the middle coefficient. -/
example : mulLinearCoeffList (2 : ℤ) 1 [3, -6] = [6, -9, -6] := by
  norm_num [mulLinearCoeffList]

/-- The generalized operation also executes over `Nat`. -/
example : mulLinearCoeffList (2 : ℕ) 3 [1, 4] = [2, 11, 12] := by
  norm_num [mulLinearCoeffList]

/-- `getD` gives zero at every index beyond the dense output. -/
example : (mulLinearCoeffList (2 : ℤ) 3 [-1, 4]).getD 8 0 = 0 := by
  rw [getD_mulLinearCoeffList]
  norm_num

private abbrev M₂ := Matrix (Fin 2) (Fin 2) ℕ

private def e01 : M₂ := !![0, 1; 0, 0]

private def e10 : M₂ := !![0, 0; 1, 0]

/-- Matrix coefficients detect the noncommutative left-factor order: the quadratic coefficient is
`e10 * e01 = E₁₁`, not `e01 * e10 = E₀₀`. -/
example : (mulLinearCoeffList e01 e10 [(1 : M₂), e01]).getD 2 0 = !![0, 0; 0, 1] := by
  rw [getD_mulLinearCoeffList]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e01, e10, Matrix.mul_apply, Fin.sum_univ_two]

example : e10 * e01 ≠ e01 * e10 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [e01, e10, Matrix.mul_apply, Fin.sum_univ_two] at h00

#print axioms Polynomial.mulLinearCoeffList
#print axioms Polynomial.length_mulLinearCoeffList
#print axioms Polynomial.getD_mulLinearCoeffList
#print axioms Polynomial.ofCoeffList_mulLinearCoeffList

end Polynomial
