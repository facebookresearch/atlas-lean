/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeSymmetrization
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Tests: Symmetrization and the approximate degree of parity
-/

@[expose] public section

open scoped BigOperators
namespace BooleanCube

set_option autoImplicit false

open BooleanCube

#print axioms exists_polynomial_eval_symmetrize
#print axioms le_totalDegree_of_approx_parityFunction
#print axioms booleanDegree_parityFunction

/-- The exact two-bit parity polynomial has total degree `2`. -/
theorem totalDegree_parity_two :
    (MvPolynomial.X 0 + MvPolynomial.X 1 -
      2 * MvPolynomial.X 0 * MvPolynomial.X 1 :
        MvPolynomial (Fin 2) ℝ).totalDegree = 2 := by
  have hX0 : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ).totalDegree = 1 := by
    rw [MvPolynomial.totalDegree_X]
  have hX1 : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ).totalDegree = 1 := by
    rw [MvPolynomial.totalDegree_X]
  have hC2 : (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 2) ℝ).totalDegree = 0 := by
    rw [MvPolynomial.totalDegree_C]
  have h1 : (1 : MvPolynomial (Fin 2) ℝ).totalDegree = 0 := by
    rw [← MvPolynomial.C_1, MvPolynomial.totalDegree_C]
  have hX0ne : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro h
    rw [h, MvPolynomial.totalDegree_zero] at hX0
    norm_num at hX0
  have hX1ne : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro h
    rw [h, MvPolynomial.totalDegree_zero] at hX1
    norm_num at hX1
  have hC2ne : MvPolynomial.C (2 : ℝ) ≠ (0 : MvPolynomial (Fin 2) ℝ) := by
    intro h
    have hcon := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℝ))) h
    simp only [MvPolynomial.eval_C, MvPolynomial.eval_zero] at hcon
    norm_num at hcon
  have hXXne : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 :=
    mul_ne_zero hX0ne hX1ne
  have hMulXX : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).totalDegree
      = (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ).totalDegree
        + (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).totalDegree := by
    apply MvPolynomial.totalDegree_mul_of_isDomain
    · exact hX0ne
    · exact hX1ne
  have h2 : (2 : MvPolynomial (Fin 2) ℝ) = MvPolynomial.C (2 : ℝ) := by
    have hC1 : MvPolynomial.C (1 : ℝ) = (1 : MvPolynomial (Fin 2) ℝ) := MvPolynomial.C_1
    have hrr : (2 : ℝ) = 1 + 1 := one_add_one_eq_two.symm
    have hpp : (2 : MvPolynomial (Fin 2) ℝ) = 1 + 1 := one_add_one_eq_two.symm
    rw [hpp, hrr, map_add, hC1]
  have hBexact : (2 * MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℝ).totalDegree = 2 := by
    rw [h2, mul_assoc]
    have hBmul : (MvPolynomial.C (2 : ℝ) * (MvPolynomial.X 0 * MvPolynomial.X 1) :
        MvPolynomial (Fin 2) ℝ).totalDegree
        = (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 2) ℝ).totalDegree
          + (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).totalDegree := by
      apply MvPolynomial.totalDegree_mul_of_isDomain
      · exact hC2ne
      · exact hXXne
    omega
  have hAddle : (MvPolynomial.X 0 + MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℝ).totalDegree
      ≤ max (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ).totalDegree
        (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).totalDegree := by
    apply MvPolynomial.totalDegree_add
  have hA1 : (MvPolynomial.X 0 + MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := by
    omega
  have hMul2le : (2 * MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ).totalDegree
      ≤ (2 : MvPolynomial (Fin 2) ℝ).totalDegree
        + (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ).totalDegree := by
    apply MvPolynomial.totalDegree_mul
  have hMul1le : (2 * MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℝ).totalDegree
      ≤ (2 * MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ).totalDegree
        + (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).totalDegree := by
    apply MvPolynomial.totalDegree_mul
  have h2le : (2 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 0 := by
    rw [show (2 : MvPolynomial (Fin 2) ℝ) = 1 + 1 from one_add_one_eq_two.symm]
    have hAdd11 : ((1 : MvPolynomial (Fin 2) ℝ) + 1).totalDegree
        ≤ max (1 : MvPolynomial (Fin 2) ℝ).totalDegree
          (1 : MvPolynomial (Fin 2) ℝ).totalDegree := by
      apply MvPolynomial.totalDegree_add
    omega
  have hB2 : (2 * MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2 := by
    omega
  have hSuble : (MvPolynomial.X 0 + MvPolynomial.X 1 - 2 * MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℝ).totalDegree
      ≤ max (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).totalDegree
        (2 * MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).totalDegree := by
    apply MvPolynomial.totalDegree_sub
  have hUpper : (MvPolynomial.X 0 + MvPolynomial.X 1 - 2 * MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2 := by
    omega
  have hLower : 2 ≤ (MvPolynomial.X 0 + MvPolynomial.X 1 - 2 * MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℝ).totalDegree := by
    have hTri := MvPolynomial.totalDegree_sub
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ)
      (MvPolynomial.X 0 + MvPolynomial.X 1 - 2 * MvPolynomial.X 0 * MvPolynomial.X 1 :
        MvPolynomial (Fin 2) ℝ)
    rw [show (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ)
        - (MvPolynomial.X 0 + MvPolynomial.X 1 - 2 * MvPolynomial.X 0 * MvPolynomial.X 1 :
          MvPolynomial (Fin 2) ℝ)
        = 2 * MvPolynomial.X 0 * MvPolynomial.X 1 from by ring] at hTri
    omega
  exact le_antisymm hUpper hLower

/-- The constant `1/2` polynomial does not `1/3`-approximate parity. -/
theorem not_approx_parity_const :
    ¬ ∀ x : BoolCube 1, |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0)
        (MvPolynomial.C (1 / 2 : ℝ)) - (if parityFunction x then 1 else 0)| ≤ 1 / 3 := by
  have hOdd : ¬ Odd (0 : ℕ) := by
    rintro ⟨k, hk⟩
    omega
  intro h
  have h0 := h fun _ => false
  simp [hammingWeight, parityFunction, hOdd, MvPolynomial.eval_C] at h0
  norm_num at h0

end BooleanCube
