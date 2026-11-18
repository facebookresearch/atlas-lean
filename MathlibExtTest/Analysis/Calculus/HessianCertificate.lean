/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Calculus.HessianCertificate
import Mathlib.Tactic.NormNum

/-!
# Hessian-certificate checks

Focused checks for
`MathlibExt.Analysis.Calculus.HessianCertificate`: the zero
function has zero model error at every point of a ball, through
the certificate with `M = 0`.

These are elaboration and non-vacuity checks, not new results.
-/

/-- Zero function, zero Hessian bound. -/
example {R : ℝ} (hR : 0 ≤ R) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R) :
    |(0 : ℝ)
      - (0 + fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) 0 z)|
      ≤ 0 * R ^ 2 / 2 :=
  hessian_error_certificate hR (fun y _ => contDiff_const.contDiffAt)
    (fun y _ => le_of_eq (by simp [ContinuousLinearMap.opNorm_zero])) hz
