/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook184Wanted

/-- **Subharmonic functions on the plane.** A function
$\varphi : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ is subharmonic if it is upper semicontinuous
and, for every point $(a, b)$ of the plane and every radius $r > 0$,

$$
\varphi(a, b) \le \frac{1}{2\pi} \int_0^{2\pi} \varphi(a + r\cos\theta, b + r\sin\theta)\, d\theta.
$$

The integral is taken to be $0$ when the integrand is not integrable over $[0, 2\pi]$, so for
such a circle the condition only says $\varphi(a, b) \le 0$. -/
def IsSubharmonic (φ : ℝ × ℝ → ℝ) : Prop :=
  UpperSemicontinuous φ ∧ ∀ (p : ℝ × ℝ) (r : ℝ), 0 < r →
    φ p ≤ (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      φ (p.1 + r * Real.cos θ, p.2 + r * Real.sin θ)

/-- **Existence of the pure second partial derivatives.** A function
$\varphi : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ has second partial derivatives if at every
point of the plane the partial derivatives $\varphi_x$ and $\varphi_y$ exist, and the partial
derivatives $\varphi_{xx} = (\varphi_x)_x$ and $\varphi_{yy} = (\varphi_y)_y$ also exist. -/
def HasSecondPartialDerivatives (φ : ℝ × ℝ → ℝ) : Prop :=
  ∀ p : ℝ × ℝ,
    DifferentiableAt ℝ (fun s => φ (s, p.2)) p.1 ∧
    DifferentiableAt ℝ (fun t => deriv (fun s => φ (s, p.2)) t) p.1 ∧
    DifferentiableAt ℝ (fun s => φ (p.1, s)) p.2 ∧
    DifferentiableAt ℝ (fun t => deriv (fun s => φ (p.1, s)) t) p.2

/--
**Subharmonic functions with second partial derivatives have nonnegative Laplacian.** Let
$\varphi : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ be subharmonic, and suppose that its
partial derivatives $\varphi_x$, $\varphi_{xx}$, $\varphi_y$ and $\varphi_{yy}$ exist at every
point of the plane. Then $\varphi_{xx}(p) + \varphi_{yy}(p) \ge 0$ for every point $p$ of the
plane.

The point is that this is not immediate outside the (dense) set where the second derivatives
are continuous.

Source: S. Saks, Problem 184 of the
Scottish Book; solved by A. Eremenko, "A problem of Stanislaw Saks",
Mat. Stud. 52 (2019), 173-175 (arXiv:1911.09530). See the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted saks184_subharmonic_laplacian_nonneg :
    ∀ φ : ℝ × ℝ → ℝ, IsSubharmonic φ → HasSecondPartialDerivatives φ →
      ∀ p : ℝ × ℝ, 0 ≤ deriv (fun t => deriv (fun s => φ (s, p.2)) t) p.1 +
        deriv (fun t => deriv (fun s => φ (p.1, s)) t) p.2

end MathlibExt.Analysis.ScottishBook184Wanted
