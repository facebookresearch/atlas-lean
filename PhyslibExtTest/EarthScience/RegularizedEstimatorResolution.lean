/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import PhyslibExt.EarthScience.RegularizedEstimatorResolution

/-!
# Regularized estimator: resolution and bias operators

Concrete consumers of
`PhyslibExt.EarthScience.RegularizedEstimatorResolution`.

## i. Overview

Nontrivial case `A = [[1, 0], [1, 1]]`, `reg = 1`, `s = [3, 4]`: the
normal matrix is `[[3, 1], [1, 2]]` with determinant `5`, so it is
invertible. Boundary case `A = 1`, `reg = 0`: the resolution operator is
`1` and the estimator recovers the model exactly.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.RegularizedEstimatorResolution`
-/

open scoped Matrix

/-- Invertibility of the normal matrix for `A = [[1, 0], [1, 1]]`,
`reg = 1`: `B = [[3, 1], [1, 2]]` with determinant `5`. -/
lemma normal_matrix_det_ne_zero :
    IsUnit ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) +
      (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det := by
  have hB : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) +
      (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = !![3, 1; 1, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  rw [hB, Matrix.det_fin_two_of]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- Nontrivial resolution: for `A = [[1, 0], [1, 1]]`, `reg = 1`,
`s = [3, 4]`, the estimator is the resolution operator applied to `s`
and its bias is the bias operator applied to `s`. -/
example :
    ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
        (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) +
        (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ *ᵥ
      ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ
        ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, 4])) =
    (((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
        (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) +
        (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ *
      ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
        (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ))) *ᵥ ![3, 4] :=
  EarthScience.regularized_estimator_eq_resolution _ _ normal_matrix_det_ne_zero

/-- Nontrivial bias: for the same `A`, `reg`, `s`, the estimator minus
the model is the bias operator applied to the model. -/
example :
    ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
        (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) +
        (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ *ᵥ
      ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *ᵥ
        ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![3, 4])) - ![3, 4] =
    (((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
        (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) +
        (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ *
      ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
        (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)) - 1) *ᵥ ![3, 4] :=
  EarthScience.regularized_estimator_bias _ _ normal_matrix_det_ne_zero

/-- Boundary case `reg = 0`, `A = 1`: the resolution operator is `1`, so
the estimator recovers the model exactly. -/
example :
    ((((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹) *
      ((1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * (1 : Matrix (Fin 2) (Fin 2) ℝ))) *ᵥ
      ![3, 4] = ![3, 4] := by
  simp
