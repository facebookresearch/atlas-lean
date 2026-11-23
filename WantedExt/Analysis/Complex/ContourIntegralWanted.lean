/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Complex.ContourIntegral

@[expose] public section

namespace MathlibExt.Analysis.Complex.ContourIntegralWanted

/-!
The contour integral `∫_γ f(z) dz` of `f : ℂ → ℂ` along a path `γ` is written as Mathlib's
curve integral of the complex-linear 1-form `z ↦ f z • id`.
-/

/--
**ML estimate for contour integrals.** Let $f : \mathbb{C} \to \mathbb{C}$ and let
$\gamma : [0, 1] \to \mathbb{C}$ be a path from $a$ to $b$ which is continuously differentiable
on $[0, 1]$, with derivative $\gamma'$ (one-sided at the endpoints). Let $M$ and $L$ be real
numbers with $|f(\gamma(t))| \le M$ and $|\gamma'(t)| \le L$ for every $t \in [0, 1]$. If
$t \mapsto f(\gamma(t))\,\gamma'(t)$ is integrable on $[0, 1]$, then
$\left|\int_\gamma f(z)\,dz\right| \le ML$, where
$\int_\gamma f(z)\,dz = \int_0^1 f(\gamma(t))\,\gamma'(t)\,dt$.

The parameter interval has length one, so $L$ bounds the length of $\gamma$.

Sources: Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable",
entry "contour integrals of continuous functions in ℂ";
L. V. Ahlfors, Complex Analysis, 3rd ed., Ch. 4, §1.1 to §1.3 (line integrals).
-/
theorem_wanted norm_contourIntegral_le
    {f : ℂ → ℂ} {a b : ℂ} {γ : Path a b} {M L : ℝ}
    (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc 0 1))
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f (γ.extend t)‖ ≤ M)
    (hγ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖derivWithin γ.extend (Set.Icc 0 1) t‖ ≤ L)
    (h_int : CurveIntegrable (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ) :
    ‖curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) γ‖ ≤ M * L

end MathlibExt.Analysis.Complex.ContourIntegralWanted
