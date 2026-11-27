/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Neyman–Scott incidental-parameter problem

Observe `n` pairs `y_{i1}, y_{i2}`, independent and Gaussian with mean `α_i` and common variance
`σ²`, where every pair has its own mean `α_i` (an incidental parameter). With
`d_i = y_{i1} - y_{i2}`, the joint maximum-likelihood estimate is `α̂_i = (y_{i1} + y_{i2}) / 2` and
`σ̂² = (1 / (4n)) ∑ d_i²` whenever some `d_i ≠ 0`; if every `d_i = 0` the likelihood is unbounded.
Since `E σ̂² = σ² / 2` and, by the strong law, `σ̂² → σ² / 2` almost surely, the maximum-likelihood
estimate of the structural parameter `σ²` is inconsistent. The differences `d_i ~ N(0, 2σ²)` do not
involve the `α_i`; their likelihood is maximized by `σ̃² = (1 / (2n)) ∑ d_i² = 2 σ̂²`, which is
consistent.

The expectation is stated in the lecture notes cited below for general `T`; the
maximum-likelihood characterization and the two limits are derived here for `T = 2`.

Sources: J. Neyman and E. L. Scott, "Consistent estimates based on partially consistent
observations", Econometrica 16 (1948) 1–32; R. Koenker, lecture notes "Incidental parameters and
dynamic bias in panel data".
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import MathlibExt.Probability.Statistics.NeymanScott

@[expose] public section

namespace WantedExt.Probability.Statistics.NeymanScottWanted

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-- **Maximum-likelihood variance estimate.** The estimate
`σ̂² = (1 / (4n)) ∑_i (y_{i1} - y_{i2})²`. -/
noncomputable def mleVariance {n : ℕ} (y : Fin n → Fin 2 → ℝ) : ℝ :=
  (∑ i, (y i 0 - y i 1) ^ 2) / (4 * n)

/-- **Difference-based variance estimate.** The conditional (difference-based) estimate
`σ̃² = (1 / (2n)) ∑_i (y_{i1} - y_{i2})²`. -/
noncomputable def conditionalVariance {n : ℕ} (y : Fin n → Fin 2 → ℝ) : ℝ :=
  (∑ i, (y i 0 - y i 1) ^ 2) / (2 * n)

/-- **The joint maximum-likelihood estimate.** For real pairs
`y i 0, y i 1`, `i < n`, with `∑_i (y_{i1} - y_{i2})² > 0`, the log-likelihood over pair means
`α ∈ ℝⁿ` and variance `s > 0` is maximized exactly at `α̂_i = (y_{i1} + y_{i2}) / 2` and
`s = σ̂² = (1 / (4n)) ∑_i (y_{i1} - y_{i2})²`: for every `α` and every `s > 0` the log-likelihood
is at most its value there, with equality only when `α = α̂` and `s = σ̂²`.

Sources: J. Neyman and E. L. Scott, "Consistent estimates based on partially consistent
observations", Econometrica 16 (1948) 1–32; the characterization is derived. -/
public theorem_wanted logLik_max {n : ℕ} (y : Fin n → Fin 2 → ℝ)
    (hd : 0 < ∑ i, (y i 0 - y i 1) ^ 2) (α : Fin n → ℝ) (s : ℝ) (hs : 0 < s) :
    logLik y α s ≤ logLik y (fun i => (y i 0 + y i 1) / 2) (mleVariance y) ∧
      (logLik y α s = logLik y (fun i => (y i 0 + y i 1) / 2) (mleVariance y) ↔
        α = (fun i => (y i 0 + y i 1) / 2) ∧ s = mleVariance y)

/-- **Inconsistency of the maximum-likelihood variance.** Let `μ` be a
probability measure and `y i t`, `i ∈ ℕ`, `t ∈ {0, 1}`, independent real random variables with
`y i t` Gaussian of mean `α_i` (arbitrary reals) and variance `σ² > 0`. Then for every `n ≥ 1`, the
estimate `σ̂²_n` from the first `n` pairs has expectation `σ² / 2`, and `σ̂²_n → σ² / 2` almost
surely as `n → ∞`.

Sources: R. Koenker, lecture notes "Incidental parameters and dynamic bias in panel data", for the
expectation, stated there for general `T`; J. Neyman and E. L. Scott, "Consistent estimates based on
partially consistent observations", Econometrica 16 (1948) 1–32; the almost-sure limit is derived.
-/
public theorem_wanted mleVariance_inconsistent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (α : ℕ → ℝ) (σsq : ℝ≥0) (hσ : 0 < σsq) (y : ℕ → Fin 2 → Ω → ℝ)
    (hind : iIndepFun (fun p : ℕ × Fin 2 => y p.1 p.2) μ)
    (hlaw : ∀ i t, μ.map (y i t) = gaussianReal (α i) σsq) :
    (∀ n : ℕ, 0 < n →
      ∫ ω, mleVariance (fun (i : Fin n) t => y i t ω) ∂μ = (σsq : ℝ) / 2) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => mleVariance (fun (i : Fin n) t => y i t ω)) atTop
        (𝓝 ((σsq : ℝ) / 2))

/-- **Consistency of the conditional estimate.** Let `μ` be a probability
measure and `y i t`, `i ∈ ℕ`, `t ∈ {0, 1}`, independent real random variables with `y i t`
Gaussian of mean `α_i` (arbitrary reals) and variance `σ² > 0`. Then the difference-based estimate
`σ̃²_n = (1 / (2n)) ∑_{i < n} (y_{i1} - y_{i2})² = 2 σ̂²_n` converges to `σ²` almost surely.

Sources: J. Neyman and E. L. Scott, "Consistent estimates based on partially consistent
observations", Econometrica 16 (1948) 1–32; derived. -/
public theorem_wanted conditionalVariance_consistent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℕ → ℝ) (σsq : ℝ≥0) (hσ : 0 < σsq)
    (y : ℕ → Fin 2 → Ω → ℝ) (hind : iIndepFun (fun p : ℕ × Fin 2 => y p.1 p.2) μ)
    (hlaw : ∀ i t, μ.map (y i t) = gaussianReal (α i) σsq) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => conditionalVariance (fun (i : Fin n) t => y i t ω)) atTop
      (𝓝 (σsq : ℝ))

end WantedExt.Probability.Statistics.NeymanScottWanted
