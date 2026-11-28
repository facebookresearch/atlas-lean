/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
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

-- `d/ds det (1 + s • M) = tr M` at `0`, for a complex `2 × 2` matrix.
example (a b c d : ℂ) :
    HasDerivAt (fun s : ℂ => (1 + s • !![a, b; c, d]).det) (a + d) 0 := by
  simpa [Matrix.trace_fin_two] using Matrix.hasDerivAt_det_one_add_smul !![a, b; c, d]

-- On the real curve `1 + s • M` it agrees with Jacobi's formula at `s = 0`, where `adj 1 = 1`.
example (M : Matrix (Fin 3) (Fin 3) ℝ) :
    deriv (fun s : ℝ => (1 + s • M).det) 0 =
      Matrix.trace ((1 : Matrix (Fin 3) (Fin 3) ℝ).adjugate * M) := by
  rw [(Matrix.hasDerivAt_det_one_add_smul M).deriv, Matrix.adjugate_one, Matrix.one_mul]
