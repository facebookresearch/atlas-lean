/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum

import MathlibExt.Analysis.Calculus.LineHessian

/-!
# Line-Hessian checks

Focused checks for `MathlibExt.Analysis.Calculus.LineHessian`: for
`f = fun y : ℝ => y^2`, `x = 0`, `v = 1`, the second line derivative
at `0` is `2`, through the public theorem.

These are elaboration and non-vacuity checks, not new results.
-/

open LineHessian

/-- The quadratic witness through the public HasDerivAt form. -/
example : HasDerivAt (deriv (fun s : ℝ => (fun y : ℝ => y ^ 2) ((0 : ℝ) + s • (1 : ℝ))))
    ((fderiv ℝ (fderiv ℝ (fun y : ℝ => y ^ 2)) ((0 : ℝ) + (0 : ℝ) • (1 : ℝ))) 1 1) 0 :=
  hasDerivAt_deriv_line (fun y : ℝ => y ^ 2) 0 1 (t := 0) (ContDiffAt.pow contDiffAt_id 2)

/-- Independent numeric check: the second line derivative of
`y ↦ y^2` at `0` in direction `1` is `2`, computed directly. -/
example : deriv (deriv (fun s : ℝ => (fun y : ℝ => y ^ 2)
      ((0 : ℝ) + s • (1 : ℝ)))) 0 = 2 := by
  have e : (fun s : ℝ => (fun y : ℝ => y ^ 2) ((0 : ℝ) + s • (1 : ℝ)))
      = fun s => s ^ 2 := by
    funext s
    simp
  have h1 : deriv (fun s : ℝ => s ^ 2) = fun s => 2 * s := by
    funext s
    rw [deriv_pow_field]
    ring
  rw [e, h1]
  simpa using HasDerivAt.deriv
    (HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_id (x := (0 : ℝ))))

/-- The norm bound on the same witness, through the public theorem. -/
example : ‖deriv (deriv (fun s : ℝ => (fun y : ℝ => y ^ 2)
      ((0 : ℝ) + s • (1 : ℝ)))) 0‖
    ≤ ‖fderiv ℝ (fderiv ℝ (fun y : ℝ => y ^ 2)) ((0 : ℝ) + (0 : ℝ) • (1 : ℝ))‖
      * ‖(1 : ℝ)‖ ^ 2 :=
  norm_deriv_deriv_line_le (fun y : ℝ => y ^ 2) 0 1 (t := 0)
    (ContDiffAt.pow contDiffAt_id 2)
