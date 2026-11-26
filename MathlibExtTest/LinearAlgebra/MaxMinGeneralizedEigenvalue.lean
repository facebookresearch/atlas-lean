/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.MaxMinGeneralizedEigenvalue
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.NormNum

open Matrix Polynomial MetaMathlibExt

private def samples (i : Fin 3) : ℝ := (2 : ℝ) ^ (i : ℕ)

private theorem samples_strictMono : StrictMono samples := by
  intro i j hij
  exact pow_lt_pow_right₀ (by norm_num) hij

private theorem samplePencil :
    ((of fun i j => max (samples i) (samples j)).map C -
      (X : ℝ[X]) • (of fun i j => min (samples i) (samples j)).map C).det =
      C ((-1 : ℝ) ^ 3 * (of fun i j => min (samples i) (samples j)).det) *
        ((X - C 2) * (X + 1) * (X + C 2)) := by
  have h := det_maxMatrix_sub_X_smul_minMatrix 3 (by decide) samples samples_strictMono
    (by norm_num [samples])
  have hr : Real.sqrt (samples (2 : Fin 3) / samples 0) = 2 := by
    have hv : samples (2 : Fin 3) / samples 0 = (2 : ℝ) ^ 2 := by norm_num [samples]
    rw [hv, Real.sqrt_sq (by norm_num)]
  simpa [hr] using h

-- The two endpoints give opposite eigenvalues; the third eigenvalue is negative one.
example :
    let p := ((of fun i j => max (samples i) (samples j)).map C -
      (X : ℝ[X]) • (of fun i j => min (samples i) (samples j)).map C).det
    Polynomial.IsRoot p 2 ∧ Polynomial.IsRoot p (-2) ∧ Polynomial.IsRoot p (-1) := by
  dsimp only
  rw [samplePencil]
  norm_num [Polynomial.IsRoot]
