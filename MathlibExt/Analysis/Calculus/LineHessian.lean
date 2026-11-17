/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Localized line-Hessian identity

## i. Overview

For `f : E → ℝ` that is `C²` at `x + t • v`, the second
derivative of the line restriction `s ↦ f (x + s • v)` at `t` is the
second Fréchet derivative applied twice to `v`, bounded by
`‖D²f‖ * ‖v‖²`.

## ii. Key results

- `LineHessian.hasDerivAt_deriv_line`: the identity in
  `HasDerivAt` form.
- `LineHessian.norm_deriv_deriv_line_le`: the absolute bound.

## iii. Table of contents

- A. Line Hessian

## iv. References

- Standard Fréchet chain rule for twice-differentiable maps
  (directional second derivative).

## A. Line Hessian
-/

@[expose] public section

namespace LineHessian

/-- Localized line-Hessian identity: if `f : E → ℝ` is `C^2` at
`x + t • v`, then the derivative of the line derivative
`s ↦ f (x + s • v)` at `t` is the second Fréchet derivative applied
twice to `v`. -/
theorem hasDerivAt_deriv_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (x v : E) {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x + t • v)) :
    HasDerivAt (deriv (fun s : ℝ => f (x + s • v)))
      ((fderiv ℝ (fderiv ℝ f) (x + t • v)) v v) t := by
  have hline_at : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => s • v) ((1 : ℝ) • v) s :=
      HasDerivAt.smul_const (hasDerivAt_id' s) v
    have h2 := HasDerivAt.const_add x h1
    simpa using h2
  have hf1 : ContDiffAt ℝ 1 (fderiv ℝ f) (x + t • v) := by
    exact hf.fderiv_right (by decide)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) (x + t • v) :=
    hf1.differentiableAt (by simp)
  have hF : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (x + t • v)) (x + t • v) :=
    hdiff.hasFDerivAt
  have hcomp : HasDerivAt ((fderiv ℝ f) ∘ (fun s : ℝ => x + s • v))
      ((fderiv ℝ (fderiv ℝ f) (x + t • v)) v) t :=
    hF.comp_hasDerivAt t (hline_at t)
  have hconst : HasDerivAt (fun _ : ℝ => v) (0 : E) t := hasDerivAt_const t v
  have hmain : HasDerivAt (fun s : ℝ => (fderiv ℝ f) (x + s • v) v)
      ((fderiv ℝ (fderiv ℝ f) (x + t • v)) v v) t := by
    have happly := hcomp.clm_apply hconst
    simpa using happly
  have hcont : ContinuousAt (fun s : ℝ => x + s • v) t := (hline_at t).continuousAt
  have hev : ∀ᶠ y in nhds (x + t • v), ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hev2 : ∀ᶠ s in nhds t, ContDiffAt ℝ 2 f (x + s • v) :=
    hcont.eventually hev
  have heq : Filter.EventuallyEq (nhds t) (deriv (fun s : ℝ => f (x + s • v)))
      (fun s => (fderiv ℝ f) (x + s • v) v) := by
    filter_upwards [hev2] with s hs
    have hdiff_f : DifferentiableAt ℝ f (x + s • v) := hs.differentiableAt (by simp)
    have hdiff_g : DifferentiableAt ℝ (fun s : ℝ => x + s • v) s := (hline_at s).differentiableAt
    have hderiv_g : deriv (fun s : ℝ => x + s • v) s = v := (hline_at s).deriv
    have hcomp2 : deriv ((f ∘ (fun s : ℝ => x + s • v))) s
        = (fderiv ℝ f (x + s • v)) (deriv (fun s : ℝ => x + s • v) s) :=
      fderiv_comp_deriv s hdiff_f hdiff_g
    simpa [Function.comp_def, hderiv_g] using hcomp2
  exact hmain.congr_of_eventuallyEq heq

/-- The second derivative of the line restriction at `t`. -/
theorem deriv_deriv_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (x v : E) {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x + t • v)) :
    deriv (deriv (fun s : ℝ => f (x + s • v))) t
      = (fderiv ℝ (fderiv ℝ f) (x + t • v)) v v := by
  exact (hasDerivAt_deriv_line f x v hf).deriv

/-- Absolute bound: the second line derivative is at most
`‖D²f (x + t • v)‖ * ‖v‖^2`. -/
theorem norm_deriv_deriv_line_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (x v : E) {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x + t • v)) :
    ‖deriv (deriv (fun s : ℝ => f (x + s • v))) t‖
      ≤ ‖fderiv ℝ (fderiv ℝ f) (x + t • v)‖ * ‖v‖ ^ 2 := by
  have hderiv : deriv (deriv (fun s : ℝ => f (x + s • v))) t
      = (fderiv ℝ (fderiv ℝ f) (x + t • v)) v v :=
    deriv_deriv_line f x v hf
  rw [hderiv]
  calc ‖((fderiv ℝ (fderiv ℝ f) (x + t • v)) v) v‖
      ≤ ‖(fderiv ℝ (fderiv ℝ f) (x + t • v)) v‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ f) (x + t • v)‖ * ‖v‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (fderiv ℝ f) (x + t • v)‖ * ‖v‖ ^ 2 := by
        rw [pow_two, mul_assoc]

end LineHessian
