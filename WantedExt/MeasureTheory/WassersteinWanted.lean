/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

/-!
# Wasserstein distances: wanted results

The Kantorovich–Rubinstein formula (Remark 6.5) and the metrization of weak convergence in `P_p`
(Theorem 6.9) of C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009,
for the Wasserstein distance of `MathlibExt.MeasureTheory.OptimalTransport.Wasserstein`.
A complete separable metric space with its Borel σ-algebra stands for Villani's Polish space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (wasserstein transportCost)

namespace MathlibExt.MeasureTheory.WassersteinWanted

/-- **Kantorovich–Rubinstein formula.** On a Polish metric space `X`, for probability measures
`μ, ν` with finite first moments, `W_1(μ, ν) = sup (∫ ψ dμ - ∫ ψ dν)` over all `1`-Lipschitz
functions `ψ : X → ℝ` (C. Villani, *Optimal Transport: Old and New*, Springer 2009,
Remark 6.5, formula (6.3), a consequence of Theorem 5.10(i) and Particular Case 5.4). The
supremum is nonnegative (take `ψ = 0`), so it is stated through `ENNReal.ofReal`. -/
theorem_wanted wasserstein_one_eq_iSup_lipschitz {X : Type*}
    [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] (μ ν : ProbabilityMeasure X) (x₀ : X)
    (hμ : ∫⁻ x, edist x₀ x ∂(μ : Measure X) < ∞) (hν : ∫⁻ x, edist x₀ x ∂(ν : Measure X) < ∞) :
    wasserstein 1 μ ν = ⨆ (ψ : X → ℝ) (_ : LipschitzWith 1 ψ),
      ENNReal.ofReal (∫ x, ψ x ∂(μ : Measure X) - ∫ x, ψ x ∂(ν : Measure X))

/-- **The Wasserstein distance metrizes weak convergence in `P_p`.** Let `X` be a Polish metric
space, `p ∈ [1, ∞)`, `x₀ ∈ X`, and let `μ_k` and `μ` be probability measures with finite
`p`-th moments `∫ d(x₀, x)^p`. Then `W_p(μ_k, μ) → 0` if and only if `μ_k → μ` weakly and
`∫ d(x₀, x)^p dμ_k → ∫ d(x₀, x)^p dμ` (C. Villani, *Optimal Transport: Old and New*, Springer
2009, Theorem 6.9 with characterization (i) of Definition 6.8). The topology on
`ProbabilityMeasure X` is the topology of weak convergence. -/
theorem_wanted tendsto_wasserstein_iff {X : Type*}
    [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] {p : ℝ} (hp : 1 ≤ p) (x₀ : X)
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμs : ∀ k, ∫⁻ x, edist x₀ x ^ p ∂(μs k : Measure X) < ∞)
    (hμ : ∫⁻ x, edist x₀ x ^ p ∂(μ : Measure X) < ∞) :
    Tendsto (fun k => wasserstein p (μs k) μ) atTop (𝓝 0) ↔
      Tendsto μs atTop (𝓝 μ) ∧
        Tendsto (fun k => ∫⁻ x, edist x₀ x ^ p ∂(μs k : Measure X)) atTop
          (𝓝 (∫⁻ x, edist x₀ x ^ p ∂(μ : Measure X)))

end MathlibExt.MeasureTheory.WassersteinWanted
