/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_det_dual_mul_mul_eq_norm_mul_det.lean`
and
`P2M/Sol/S_Algebra_det_dual_mul_mul_eq_norm_mul_det.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Norm.Basic

/-!
# Determinant of a scaled dual pairing

For a basis `b` of a commutative algebra `A` over `R`, a linear form
`τ` on `A`, and `c : A`, scaling the first factor in the pairing
`(i, j) ↦ τ (b i * b j)` by `c` multiplies its determinant by the
norm of `c`: the scaled matrix is the product of the left-multiplication
matrix of `c` with the unscaled matrix.
-/

@[expose] public section

open Module

private theorem mul_basis_eq_sum {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R A) (c : A)
    (j : ι) : c * b j = ∑ k, Algebra.leftMulMatrix b c k j • b k := by
  conv_lhs => rw [← b.sum_repr (c * b j)]
  simp only [Algebra.leftMulMatrix_eq_repr_mul]

private theorem of_dual_mul_mul_eq {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι R A)
    (τ : Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)) =
      (Algebra.leftMulMatrix b c).transpose * Matrix.of fun i j => τ (b i * b j) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [mul_basis_eq_sum b c i, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]

/-- The determinant of the pairing `(i, j) ↦ τ (c * b i * b j)` is the
norm of `c` times the determinant of the unscaled pairing. -/
theorem Algebra.det_dual_mul_mul_eq_norm_mul_det (R : Type*) [CommRing R]
    (A : Type*) [CommRing A] [Algebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R A) (τ : Module.Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)).det =
      Algebra.norm R c * (Matrix.of fun i j => τ (b i * b j)).det := by
  rw [of_dual_mul_mul_eq b τ c, Matrix.det_mul, Matrix.det_transpose,
    Algebra.norm_eq_matrix_det b]
