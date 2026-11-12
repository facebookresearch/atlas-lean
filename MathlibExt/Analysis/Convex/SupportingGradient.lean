/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Order.Filter.Extr
public import MathlibExt.Analysis.Convex.KarushKuhnTucker

/-!
# Supporting gradients certify global optimality

If an affine minorant `y ↦ f x + g (y - x)` supports `f` on a feasible set `S` at a feasible point
`x`, and `g` is nonnegative on every feasible direction `y - x`, then `x` minimizes `f` on `S`.

## i. Overview

For a convex function differentiable at `x`, the derivative is a supporting gradient by the
first-order convexity inequality `ConvexOn.add_fderiv_sub_le`
(`MathlibExt.Analysis.Convex.KarushKuhnTucker`). Together these give the first-order optimality
criterion for differentiable convex problems: on a convex feasible set (`ConvexOn ℝ S f` includes
`Convex ℝ S`), a feasible point at which the derivative is nonnegative in every feasible direction
is a global minimizer. The certificate itself needs no convexity of `S` or `f`; the criterion
fails without convexity of `f` (see the tests).

## ii. Main results

* `MathlibExt.SupportingGradient.isMinOn_of_isSupportingGradient`
* `MathlibExt.SupportingGradient.isSupportingGradient_fderiv`
* `MathlibExt.SupportingGradient.isMinOn_of_convexOn_of_fderiv_nonneg`

## iii. References

* S. Boyd and L. Vandenberghe, *Convex Optimization* (2004), §3.1.3 (eq. 3.2) and §4.2.3
  (eq. 4.21).
-/

@[expose] public section

namespace MathlibExt.SupportingGradient

/-- `g` is a *supporting gradient* of `f` at `x` relative to the feasible set `S`: the affine
minorant `y ↦ f x + g (y - x)` lies below `f` on `S`. -/
def IsSupportingGradient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (S : Set E) (x : E) (g : E →L[ℝ] ℝ) : Prop :=
  ∀ y ∈ S, f x + g (y - x) ≤ f y

/-- **Certificate of global optimality.** If `g` supports `f` at `x` on `S` and `g` is
nonnegative on every feasible direction `y - x` (`y ∈ S`), then `x` minimizes `f` on `S`. For a
feasible candidate `x ∈ S` this says `x` is a global minimizer on `S`; the inequality does not
need membership, and, as in Mathlib's `IsMinOn`, membership is not part of the conclusion. -/
theorem isMinOn_of_isSupportingGradient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {S : Set E} {x : E} {g : E →L[ℝ] ℝ} (hsupp : IsSupportingGradient f S x g)
    (hdir : ∀ y ∈ S, 0 ≤ g (y - x)) : IsMinOn f S x := by
  rw [isMinOn_iff]
  intro y hy
  have h1 := hsupp y hy
  have h2 := hdir y hy
  linarith

/-- For a convex function differentiable at a feasible point, the derivative is a supporting
gradient. -/
theorem isSupportingGradient_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {S : Set E} {x : E} (hf : ConvexOn ℝ S f) (hx : x ∈ S)
    (hd : DifferentiableAt ℝ f x) : IsSupportingGradient f S x (fderiv ℝ f x) := by
  intro y hy
  exact ConvexOn.add_fderiv_sub_le hf hx hy hd

/-- **First-order sufficiency.** A feasible point of a convex function, differentiable there,
at which the derivative is nonnegative in every feasible direction, is a global minimizer on the
feasible set. -/
theorem isMinOn_of_convexOn_of_fderiv_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {S : Set E} {x : E} (hf : ConvexOn ℝ S f) (hx : x ∈ S)
    (hd : DifferentiableAt ℝ f x) (hdir : ∀ y ∈ S, 0 ≤ fderiv ℝ f x (y - x)) :
    IsMinOn f S x := by
  exact isMinOn_of_isSupportingGradient (isSupportingGradient_fderiv hf hx hd) hdir

end MathlibExt.SupportingGradient
