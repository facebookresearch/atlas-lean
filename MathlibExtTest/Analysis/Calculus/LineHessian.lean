/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.ContDiff.Operations
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
