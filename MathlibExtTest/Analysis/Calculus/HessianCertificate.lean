/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Calculus.HessianCertificate
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Hessian-certificate checks

Focused checks for
`MathlibExt.Analysis.Calculus.HessianCertificate`: the zero
function has zero model error through the certificate with
`M = 0`, and the quadratic `‖z‖ ^ 2` attains the bound with
`M = 2` at a unit boundary point.

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

/-- Nonzero quadratic attaining the bound: for `g z = ‖z‖ ^ 2`
with Hessian bound `M = 2`, radius `1`, and a unit boundary
point, the model error is `1`, equal to `2 * 1 ^ 2 / 2`. -/
example : |(1 : ℝ) - 0| ≤ 2 * (1 : ℝ) ^ 2 / 2 := by
  have hz : EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
      ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    simp [Metric.mem_closedBall, dist_eq_norm]
  have hH : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2))
        (1 : ℝ),
      ‖fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) => ‖z‖ ^ 2))
        y‖ ≤ 2 := by
    intro y _
    have hder : fderiv ℝ
        (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) => ‖z‖ ^ 2)) y
        = (2 : ℕ) • innerSL ℝ := by
      rw [fderiv_norm_sq]
      simpa [FunLike.coe_smul] using
        ((2 : ℕ) • innerSL ℝ
          (E := EuclideanSpace ℝ (Fin 2))).hasFDerivAt.fderiv
    rw [hder]
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
    intro x
    calc ‖((2 : ℕ) • innerSL ℝ (E := EuclideanSpace ℝ (Fin 2))) x‖
        = ‖(2 : ℕ) • (innerSL ℝ (E := EuclideanSpace ℝ (Fin 2)) x)‖ := by simp
      _ ≤ 2 * ‖innerSL ℝ (E := EuclideanSpace ℝ (Fin 2)) x‖ := norm_nsmul_le
      _ = 2 * ‖x‖ := by simp [innerSL_apply_norm]
  have h := hessian_error_certificate
    (g := fun z : EuclideanSpace ℝ (Fin 2) => ‖z‖ ^ 2) (M := 2)
    (R := 1) (by norm_num)
    (fun y _ => (contDiff_norm_sq ℝ).contDiffAt) hH hz
  simpa [fderiv_norm_sq_apply] using h
