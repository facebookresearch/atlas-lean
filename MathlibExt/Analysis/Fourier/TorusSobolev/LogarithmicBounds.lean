/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.TorusSobolev.Basic

/-!
# One-log and double-log bounds on actual torus functions

The coefficients quantify uniformly over the full zero-mean spectral `H²` class.
The ratio guards exclude zero gradient energy and keep the logarithms in their
source domain. These definitions assert no sharpness or existence theorem.
-/

@[expose] public section

noncomputable section

namespace TorusSobolev

/-- **One-log bound with coefficient $c$ and constant $K$.** For real numbers $c$ and $K$, the
one-log bound holds when every continuous function $u : \mathbb{T} \to \mathbb{R}$ on the torus
$\mathbb{T} = (\mathbb{R}/2\pi\mathbb{Z})^2$ that is a zero-mean $H^2$ function, has gradient energy
$E(u) > 0$ and has frequency ratio $\delta(u) \ge 1$ (the Laplacian energy divided by $E(u)$)
satisfies, at every point $x \in \mathbb{T}$,
$$u(x)^2 \le c\,E(u)\bigl(\log\delta(u) + K\bigr).$$ -/
def OneLogBound (c K : ℝ) : Prop :=
  ∀ u : C(Torus, ℝ), IsZeroMeanH2 u → 0 < gradientEnergy u → 1 ≤ frequencyRatio u →
    ∀ x : Torus, (u x) ^ 2 ≤ c * gradientEnergy u * (Real.log (frequencyRatio u) + K)

/-- The double-log coefficient with the endpoint-safe `1 + log δ`. -/
def DoubleLogBound (a L : ℝ) : Prop :=
  ∀ u : C(Torus, ℝ), IsZeroMeanH2 u → 0 < gradientEnergy u → 1 ≤ frequencyRatio u →
    ∀ x : Torus, (u x) ^ 2 ≤ gradientEnergy u / (4 * Real.pi) *
      (Real.log (frequencyRatio u) + a * Real.log (1 + Real.log (frequencyRatio u)) + L)

/-- **Optimal one-log coefficient.** The infimum, taken in the extended reals, of all real
numbers $c$ for which there is a real constant $K$ such that the one-log bound with
coefficient $c$ and constant $K$ holds. It is $+\infty$ when no such $c$ exists. -/
def oneLogLeadingCoefficientInfimum : EReal :=
  sInf ((fun c : ℝ ↦ (c : EReal)) '' {c | ∃ K : ℝ, OneLogBound c K})

end TorusSobolev
