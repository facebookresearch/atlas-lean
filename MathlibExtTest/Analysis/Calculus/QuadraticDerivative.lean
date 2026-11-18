/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

import MathlibExt.Analysis.Calculus.QuadraticDerivative

/-!
# Quadratic-derivative checks

Focused checks for `MathlibExt.Analysis.Calculus.QuadraticDerivative`:
with `C` the identity on `Fin 2` and `x(s)` the path `(s, 1)`, the
derivative at time `t` is `t`, through the public theorem.

These are elaboration and non-vacuity checks, not new results.
-/

open QuadraticDerivative

/-- Identity witness through the public `deriv` form. -/
example (t : ℝ) :
    deriv (fun s => MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm (fun i j : Fin 2 => if i = j then (1 : ℝ) else 0)
      (fun (i : Fin 2) => if i = 0 then s else 1) / 2) t = t := by
  have hC : Matrix.IsSymm
      ((fun i j : Fin 2 => if i = j then (1 : ℝ) else 0) :
        Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hx : ∀ i : Fin 2, HasDerivAt (fun s => if i = 0 then s else (1 : ℝ))
      (if i = 0 then (1 : ℝ) else 0) t := by
    intro i
    by_cases h : i = 0
    · simp [h]
      exact hasDerivAt_id t
    · simp [h]
      exact hasDerivAt_const t (1 : ℝ)
  rw [quadForm_half_deriv_eq _ hC _ _ t hx]
  simp [Fin.sum_univ_two]
