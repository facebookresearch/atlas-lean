/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Matrix.DeterminantDerivative
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Inverse and log-determinant along a matrix curve

At a point where a real matrix curve is differentiable and its value is invertible, its
velocity determines the derivatives of the inverse and the logarithm of the absolute
determinant. No commutation or positive-definiteness hypothesis is needed.
-/

@[expose] public section

open scoped Matrix.Norms.Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : ℝ → Matrix n n ℝ}
  {H : Matrix n n ℝ} {t : ℝ}

/-- If a real matrix curve is differentiable at `t` with velocity `H` and `A t` is invertible,
the derivative of the inverse at `t` is `−(A t)⁻¹ H (A t)⁻¹`. The factors need not commute. -/
theorem hasDerivAt_nonsingInv_curve (h : HasDerivAt A H t) (hu : IsUnit (A t)) :
    HasDerivAt (fun s => (A s)⁻¹) (-(A t)⁻¹ * H * (A t)⁻¹) t := by
  have hd := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  rw [hu.unit_spec] at hd
  simpa [nonsing_inv_eq_ringInverse, ContinuousLinearMap.mulLeftRight_apply,
    Function.comp_def, Matrix.coe_units_inv, hu.unit_spec] using! hd.comp_hasDerivAt t h

/-- If a real matrix curve is differentiable at `t` with velocity `H` and `A t` is invertible,
the logarithm of its absolute determinant has derivative `tr((A t)⁻¹ H)` there. For positive
determinant this is the usual log determinant; `Real.log` gives the same formula at either sign. -/
theorem hasDerivAt_logDet_curve (h : HasDerivAt A H t) (hu : IsUnit (A t)) :
    HasDerivAt (fun s => Real.log (A s).det) (((A t)⁻¹ * H).trace) t := by
  have hdet := (isUnit_iff_isUnit_det _).mp hu
  let d : ContinuousMultilinearMap ℝ (fun _ : n => n → ℝ) ℝ :=
    { toMultilinearMap := (Matrix.detRowAlternating : (n → ℝ) [⋀^n]→ₗ[ℝ] ℝ).toMultilinearMap
      cont := (continuous_id : Continuous (fun B : Matrix n n ℝ => B)).matrix_det }
  have hd : DifferentiableAt ℝ (fun s => (A s).det) t :=
    ((d.hasFDerivAt (A t)).comp_hasDerivAt t h).differentiableAt
  have hh := hd.hasDerivAt.log hdet.ne_zero
  rw [deriv_det_eq_trace_adjugate_mul _ _ h.differentiableAt] at hh
  erw [h.deriv] at hh
  convert hh using 1
  simp [inv_def, Ring.inverse_eq_inv, div_eq_inv_mul]

end Matrix
