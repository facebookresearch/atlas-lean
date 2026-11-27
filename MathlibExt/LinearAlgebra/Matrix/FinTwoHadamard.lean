/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Normalized two-dimensional Hadamard matrix

The matrix H=(1/√2)[[1,1],[1,-1]] over ℂ satisfies HᴴH=HHᴴ=I. It defines the normalized
Hadamard unitary on Fin 2.
-/

@[expose] public section

namespace Matrix

private lemma sqrt_two_pos : 0 < Real.sqrt 2 :=
  Real.sqrt_pos.mpr (by norm_num)

private lemma sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 :=
  ne_of_gt sqrt_two_pos

private lemma sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

private lemma complex_sqrt_two_sq :
    (Real.sqrt 2 : Complex) ^ 2 = 2 := by
  calc (Real.sqrt 2 : Complex) ^ 2
      = ((Real.sqrt 2 ^ 2 : ℝ) : Complex) := by
        rw [← Complex.ofReal_pow]
    _ = ((2 : ℝ) : Complex) := by rw [sqrt_two_sq]
    _ = 2 := by simp

private lemma complex_sqrt_two_ne_zero :
    (Real.sqrt 2 : Complex) ≠ 0 := by
  rw [Ne, Complex.ofReal_eq_zero]
  exact sqrt_two_ne_zero

private lemma star_ofReal (r : ℝ) :
    star (r : Complex) = (r : Complex) := by
  rw [Complex.star_def, Complex.conj_ofReal]

/-- **Normalized Hadamard matrix on two coordinates.**

The complex matrix finTwoHadamard on Fin 2 is (1/√2)[[1,1],[1,-1]].
-/
noncomputable def finTwoHadamard : Matrix (Fin 2) (Fin 2) Complex :=
  fun i j =>
    match i, j with
    | 0, 0 => ((1 : ℝ) / Real.sqrt 2 : Complex)
    | 0, 1 => ((1 : ℝ) / Real.sqrt 2 : Complex)
    | 1, 0 => ((1 : ℝ) / Real.sqrt 2 : Complex)
    | 1, 1 => ((-1 : ℝ) / Real.sqrt 2 : Complex)

private lemma finTwoHadamard_entry_star_eq (i j : Fin 2) :
    star (finTwoHadamard j i) = finTwoHadamard j i := by
  fin_cases i <;> fin_cases j <;>
    simp [finTwoHadamard, star_ofReal]

private lemma finTwoHadamard_symm (i j : Fin 2) :
    finTwoHadamard i j = finTwoHadamard j i := by
  fin_cases i <;> fin_cases j <;> rfl

private lemma star_finTwoHadamard :
    star finTwoHadamard = finTwoHadamard := by
  ext i j
  rw [Matrix.star_apply]
  rw [finTwoHadamard_entry_star_eq]
  rw [finTwoHadamard_symm]

theorem finTwoHadamard_mem_unitaryGroup :
    finTwoHadamard ∈ Matrix.unitaryGroup (Fin 2) Complex := by
  have hStar : star finTwoHadamard = finTwoHadamard :=
    star_finTwoHadamard
  have hSq : (Real.sqrt 2 : Complex) ^ 2 = 2 :=
    complex_sqrt_two_sq
  rw [Matrix.mem_unitaryGroup_iff, hStar]
  ext i j
  fin_cases i
  · fin_cases j
    · simp only [Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, finTwoHadamard] at *
      simp at *
      field_simp
      rw [hSq]
      norm_num
    · simp only [Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, finTwoHadamard] at *
      simp at *
      field_simp
      rw [hSq]
      norm_num
  · fin_cases j
    · simp only [Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, finTwoHadamard] at *
      simp at *
      field_simp
      rw [hSq]
      norm_num
    · simp only [Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, finTwoHadamard] at *
      simp at *
      field_simp
      rw [hSq]
      norm_num

/-- **Two-dimensional Hadamard unitary.**

The element finTwoHadamardUnitary∈U(2,ℂ) has matrix (1/√2)[[1,1],[1,-1]].
-/
noncomputable def finTwoHadamardUnitary :
    Matrix.unitaryGroup (Fin 2) Complex :=
  ⟨finTwoHadamard, finTwoHadamard_mem_unitaryGroup⟩

end Matrix
