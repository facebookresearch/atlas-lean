/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Mul
import MathlibExt.Analysis.Matrix.DeterminantDerivative

open scoped Matrix.Norms.Elementwise

-- The one-by-one matrix curve `[t]` is singular at zero, but its determinant derivative is one.
example : deriv (fun t : ℝ => (t • (1 : Matrix (Fin 1) (Fin 1) ℝ)).det) 0 = 1 := by
  let A (t : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := t • 1
  have h := (hasDerivAt_id (0 : ℝ)).smul_const (1 : Matrix (Fin 1) (Fin 1) ℝ)
  have hA : DifferentiableAt ℝ A 0 := h.differentiableAt
  have hD : deriv A 0 = (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
    h.deriv.trans (one_smul ℝ _)
  change deriv (fun t => (A t).det) 0 = 1
  rw [Matrix.deriv_det_eq_trace_adjugate_mul A 0 hA, hD]
  simp [Matrix.adjugate_fin_one, Matrix.trace]
