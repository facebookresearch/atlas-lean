/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
import MathlibExt.MeasureTheory.Function.ConditionalExpectation.BestPredictor

/-!
# Orthogonality of square-integrable martingale increments

If `X` is a martingale with `E[X_n^2] < ∞` for all `n`, then for `m ≤ n`
the increment `X_n - X_m` is orthogonal in `L²` to every `ℱ_m`-measurable
square-integrable random variable `Y`: `E[(X_n - X_m) * Y] = 0`. Taking
`Y = X_m` gives the variance-of-increment identity
`E[(X_n - X_m)^2] = E[X_n^2] - E[X_m^2]`.

## Source

This formalizes the target "Theorem (Orthogonality of martingale increments)"
(Lecture 28) of `v1/Atlas/TheoryOfProbability/targets.yaml`, whose v1
formalization is `v1/Atlas/TheoryOfProbability/code/MartingaleOrthogonality.lean`
(`martingale_orthogonal_general`). The integral square identity
specializes the conditional-mean Pythagorean identity. Both proofs reuse
the general API in
`MathlibExt/MeasureTheory/Function/ConditionalExpectation/BestPredictor.lean`.

## Main results

* `MeasureTheory.Martingale.integral_sub_mul_eq_zero`: orthogonality of
  martingale increments.
* `MeasureTheory.Martingale.integral_sub_sq_eq`: `E[(X_n - X_m)^2] =
  E[X_n^2] - E[X_m^2]` for `m ≤ n`.
-/

@[expose] public section

open MeasureTheory Filter

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Orthogonality of martingale increments.** Let $(\Omega, \mu)$ be a probability space with a
filtration $(\mathcal{F}_n)_{n \in \mathbb{N}}$, and let $(X_n)_{n \in \mathbb{N}}$ be a real-valued
martingale with respect to $(\mathcal{F}_n)$ and $\mu$ such that $\mathbb{E}[X_k^2] < \infty$ for
every $k$. Let $m \le n$ and let $Y$ be an $\mathcal{F}_m$-measurable real random variable with
$\mathbb{E}[Y^2] < \infty$. Then $\mathbb{E}[(X_n - X_m) Y] = 0$. In other words, the increment
$X_n - X_m$ is orthogonal in $L^2$ to every square-integrable $\mathcal{F}_m$-measurable random
variable.

Source: Lecture 28, orthogonality of martingale increments. -/
theorem Martingale.integral_sub_mul_eq_zero
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hmart : Martingale X ℱ μ)
    {m n : ℕ} (hmn : m ≤ n)
    {Y : Ω → ℝ} (hY_meas : StronglyMeasurable[ℱ m] Y)
    (hY_int : Integrable (fun ω => (Y ω) ^ 2) μ)
    (hX_sq : ∀ k, Integrable (fun ω => (X k ω) ^ 2) μ) :
    ∫ ω, (X n ω - X m ω) * Y ω ∂μ = 0 := by
  have hn : MemLp (X n) 2 μ :=
    (memLp_two_iff_integrable_sq (hmart.integrable n).aestronglyMeasurable).mpr (hX_sq n)
  have hY : MemLp Y 2 μ :=
    (memLp_two_iff_integrable_sq (hY_meas.mono (ℱ.le m)).aestronglyMeasurable).mpr hY_int
  calc ∫ ω, (X n ω - X m ω) * Y ω ∂μ
      = ∫ ω, (X n ω - μ[X n | ℱ m] ω) * Y ω ∂μ :=
        integral_congr_ae ((hmart.condExp_ae_eq hmn).mono fun ω hω => by dsimp only; rw [hω])
    _ = 0 := integral_sub_condExp_mul_eq_zero (ℱ.le m) hn hY hY_meas

/-- **Pythagorean identity for martingale increments.** Let $(\Omega, \mu)$ be a probability
space with a filtration $(\mathcal{F}_n)_{n \in \mathbb{N}}$, and let $(X_n)_{n \in \mathbb{N}}$ be
a real-valued martingale with respect to $(\mathcal{F}_n)$ and $\mu$ such that
$\mathbb{E}[X_k^2] < \infty$ for every $k$. Then for all $m \le n$,
$$
\mathbb{E}[(X_n - X_m)^2] = \mathbb{E}[X_n^2] - \mathbb{E}[X_m^2].
$$

This is the orthogonality of martingale increments applied to the $\mathcal{F}_m$-measurable
random variable $X_m$, expanded. -/
theorem Martingale.integral_sub_sq_eq
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hmart : Martingale X ℱ μ)
    {m n : ℕ} (hmn : m ≤ n)
    (hX_sq : ∀ k, Integrable (fun ω => (X k ω) ^ 2) μ) :
    ∫ ω, (X n ω - X m ω) ^ 2 ∂μ =
      ∫ ω, (X n ω) ^ 2 ∂μ - ∫ ω, (X m ω) ^ 2 ∂μ := by
  have hn : MemLp (X n) 2 μ :=
    (memLp_two_iff_integrable_sq (hmart.integrable n).aestronglyMeasurable).mpr (hX_sq n)
  have hp := integral_sq_sub_eq_integral_sq_sub_condExp_add (ℱ.le m)
    (g := (0 : Ω → ℝ)) hn MemLp.zero stronglyMeasurable_zero
  have hr : ∫ ω, (X n ω - μ[X n | ℱ m] ω) ^ 2 ∂μ =
      ∫ ω, (X n ω - X m ω) ^ 2 ∂μ :=
    integral_congr_ae ((hmart.condExp_ae_eq hmn).mono fun ω hω => by dsimp only; rw [hω])
  have hc : ∫ ω, (μ[X n | ℱ m] ω) ^ 2 ∂μ = ∫ ω, (X m ω) ^ 2 ∂μ :=
    integral_congr_ae ((hmart.condExp_ae_eq hmn).mono fun ω hω => by dsimp only; rw [hω])
  simp only [Pi.zero_apply, sub_zero] at hp
  rw [hr, hc] at hp
  linarith

end MeasureTheory
