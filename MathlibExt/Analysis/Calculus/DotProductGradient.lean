/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Gradients of real functions on `ι → ℝ`

In Mathlib `ι → ℝ` carries the sup norm and is not an inner product space, so `HasGradientAt` does
not apply to functions on it. This file differentiates them in the Fréchet sense (`HasFDerivAt`),
with a gradient `g` represented by the continuous linear functional `dotL g : v ↦ v ⬝ᵥ g`, and
transfers the result to Mathlib's gradient API on `EuclideanSpace ℝ ι`.

* `dotL`, `dotL_apply`, `hasFDerivAt_dotProduct`: the functional `v ↦ v ⬝ᵥ x` and the derivative
  of a linear form.
* `hasGradientAt_ofLp`: a Fréchet derivative `dotL g` at `z` is the gradient `g` of the
  corresponding function on `EuclideanSpace ℝ ι` (`HasGradientAt`).
* `hasDerivAt_line_of_hasFDerivAt`: the directional derivative along `t ↦ z + t • v` is `v ⬝ᵥ g`.
-/

@[expose] public section

namespace Real

open Finset

variable {ι : Type*} [Fintype ι]

/-- **The dot product with a fixed vector.** For a finite type $\iota$ and a vector
$x \in \mathbb{R}^\iota$, this is the map $v \mapsto v \cdot x = \sum_{i \in \iota} v_i x_i$,
as a continuous linear functional $\mathbb{R}^\iota \to \mathbb{R}$. -/
noncomputable def dotL (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, x i • ContinuousLinearMap.proj i

@[simp]
theorem dotL_apply (x v : ι → ℝ) : dotL x v = v ⬝ᵥ x := by
  simp [dotL, dotProduct, mul_comm]

theorem hasFDerivAt_dotProduct (x w : ι → ℝ) : HasFDerivAt (fun w => w ⬝ᵥ x) (dotL x) w := by
  convert (dotL x).hasFDerivAt (x := w) using 1
  funext v
  simp

/-- **A Fréchet derivative given by a dot product is a gradient.** Let $\iota$ be a finite type,
let $f : \mathbb{R}^\iota \to \mathbb{R}$ and $g, z \in \mathbb{R}^\iota$, and suppose that, for the
sup norm on $\mathbb{R}^\iota$, $f$ is Fréchet differentiable at $z$ with derivative
$v \mapsto v \cdot g$. Then $f$, viewed as a function on the Euclidean space $\mathbb{R}^\iota$ with
inner product $\langle v, w \rangle = \sum_{i \in \iota} v_i w_i$, has gradient $g$ at $z$. -/
theorem hasGradientAt_ofLp {f : (ι → ℝ) → ℝ} {g z : ι → ℝ} (hf : HasFDerivAt f (dotL g) z) :
    HasGradientAt (fun w : EuclideanSpace ℝ ι => f (WithLp.ofLp w)) (WithLp.toLp 2 g)
      (WithLp.toLp 2 z) := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have e : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι) (WithLp.toLp 2 g) =
      (dotL g).comp (EuclideanSpace.equiv ι ℝ : EuclideanSpace ℝ ι →L[ℝ] ι → ℝ) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [e]
  exact hf.comp (WithLp.toLp 2 z) (EuclideanSpace.equiv ι ℝ).hasFDerivAt

/-- **Directional derivative from the gradient.** Let $\iota$ be a finite type, let
$f : \mathbb{R}^\iota \to \mathbb{R}$ and $g, z \in \mathbb{R}^\iota$, and suppose $f$ is Fréchet
differentiable at $z$ with derivative $w \mapsto w \cdot g$. Then for every
$v \in \mathbb{R}^\iota$, the function $t \mapsto f(z + t v)$ on $\mathbb{R}$ has derivative
$v \cdot g$ at $t = 0$. -/
theorem hasDerivAt_line_of_hasFDerivAt {f : (ι → ℝ) → ℝ} {g z : ι → ℝ}
    (hf : HasFDerivAt f (dotL g) z) (v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => f (z + t • v)) (v ⬝ᵥ g) 0 := by
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have := (by simpa using hf : HasFDerivAt f (dotL g) (z + (0 : ℝ) • v)).comp_hasDerivAt 0 hline
  rw [dotL_apply] at this
  exact this

end Real
