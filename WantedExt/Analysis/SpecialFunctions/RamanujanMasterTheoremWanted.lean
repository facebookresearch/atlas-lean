/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Batteries.Util.ProofWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Ramanujan's master theorem.** Let $a$ and $b$ be real numbers with $0 < a < b$, and let
$s$ be a complex number with $a < \operatorname{Re} s < b$. Let $\varphi$ be a function from
$\mathbb{C}$ to $\mathbb{C}$ that is analytic on the half-plane $\operatorname{Re} z > -b$, and
suppose there are real constants $C > 0$ and $P < \pi$ such that
$|\varphi(u + iv)| \le C e^{P|v|}$ for all real $u$ and $v$ with $u > -b$. Let $F$ be a function
from $\mathbb{R}$ to $\mathbb{C}$ such that for every real $x > 0$ the series
$\sum_{k=0}^{\infty} \varphi(k)\,(-x)^k / k!$ converges unconditionally to $F(x)$, and suppose
that $x \mapsto x^{s-1} F(x)$ is Lebesgue integrable on $(0, \infty)$, where
$x^{s-1} = e^{(s-1)\log x}$. Then

$$\int_0^\infty x^{s-1} F(x)\,dx = \Gamma(s)\,\varphi(-s).$$

This is a specialization of the theorem: the growth bound on $\varphi$ is uniform in
$\operatorname{Re} z$, and integrability of $x^{s-1} F(x)$ is assumed rather than derived.

Source: https://en.wikipedia.org/wiki/Ramanujan%27s_master_theorem
(Raw: `int_0^infty x^{s-1} sum_k phi(k)(-x)^k/k! dx = Gamma(s) phi(-s)`.) -/
theorem_wanted Ramanujan_master_theorem
    (φ : ℂ → ℂ) (F : ℝ → ℂ) (a b : ℝ) (s : ℂ)
    (ha : 0 < a) (hab : a < b)
    (hs : a < s.re ∧ s.re < b)
    (hφ : AnalyticOn ℂ φ {z : ℂ | -b < z.re})
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∃ P : ℝ, P < Real.pi ∧
      ∀ u v : ℝ, -b < u → ‖φ (Complex.mk u v)‖ ≤ C * Real.exp (P * |v|))
    (hF : ∀ x : ℝ, 0 < x →
      HasSum (fun k : ℕ => φ (k : ℂ) * (-(x : ℂ)) ^ k / (k.factorial : ℂ)) (F x))
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => ((x : ℂ) ^ (s - 1) * F x : ℂ))
      (Set.Ioi (0 : ℝ)) MeasureTheory.volume)
    : ∫ x in Set.Ioi (0 : ℝ), ((x : ℂ) ^ (s - 1) * F x) ∂MeasureTheory.volume
      = Complex.Gamma s * φ (-s)

end

end MetaMathlibExt
