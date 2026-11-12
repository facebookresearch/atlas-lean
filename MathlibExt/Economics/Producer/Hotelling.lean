/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Envelope
public import MathlibExt.Analysis.Calculus.DotProductGradient
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Hotelling's lemma

A competitive (price-taking) firm chooses a net supply vector `y` from a production set
`Y : Set (ι → ℝ)` (positive entries are outputs, negative entries inputs) to maximize profit
`p ⬝ᵥ y`. If `π` is the profit function near `p₀` (the least upper bound of `p ⬝ᵥ y` over `Y`),
`y₀ ∈ Y` attains the maximum at `p₀`, and `π` is differentiable at `p₀` with derivative `π'`, then
`π' v = y₀ ⬝ᵥ v` for every direction `v`: the price gradient of profit is the optimal net supply.
Consequently the optimal net supply at `p₀` is unique.

The proof is the envelope argument (`Economics.hasFDerivAt_eq_of_eventually_le_of_eq`): near `p₀`
the linear function `p ↦ p ⬝ᵥ y₀` lies below `π` and touches it at `p₀`. Price-taking is a premise
of the model; no convexity of `Y` and no sign condition on prices is used.

## Main results

* `Economics.Producer.hasFDerivAt_profit_eq_netSupply`: Hotelling's lemma.
* `Economics.Producer.netSupply_unique_of_hasFDerivAt`: uniqueness of the optimal net supply.
* `Economics.Producer.hasFDerivAt_profit_eq_dotL`: the derivative of profit is `Real.dotL y₀`,
  the repository's gradient representation on `ι → ℝ`.

## References

* H. Hotelling, *Edgeworth's taxation paradox and the nature of demand and supply functions*,
  J. Political Economy 40 (1932), 577–616.
* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Proposition 5.C.1.
-/

@[expose] public section

open Filter Topology

namespace Economics.Producer

/-- **Hotelling's lemma.** Let `π` be the profit function of the production
set `Y` on a neighborhood of `p₀` (the supremum of `p ⬝ᵥ y` over `y ∈ Y`), and
let `y₀ ∈ Y` attain the maximal profit at `p₀`. If `π` is differentiable at
`p₀` with derivative `π'`, then `π' v = y₀ ⬝ᵥ v` for every direction `v`: the
price gradient of profit is the optimal net supply. -/
theorem hasFDerivAt_profit_eq_netSupply {ι : Type*} [Fintype ι]
    {Y : Set (ι → ℝ)} {π : (ι → ℝ) → ℝ} {p₀ y₀ : ι → ℝ}
    {π' : (ι → ℝ) →L[ℝ] ℝ}
    (hπ : ∀ᶠ p in 𝓝 p₀, IsLUB ((fun y => p ⬝ᵥ y) '' Y) (π p))
    (hy₀ : y₀ ∈ Y) (hprofit : p₀ ⬝ᵥ y₀ = π p₀)
    (hdiff : HasFDerivAt π π' p₀) :
    ∀ v, π' v = y₀ ⬝ᵥ v := by
  have hle : ∀ᶠ p in 𝓝 p₀, (fun p => p ⬝ᵥ y₀) p ≤ π p := by
    filter_upwards [hπ] with p hp
    exact hp.1 (Set.mem_image_of_mem _ hy₀)
  have heq := Economics.hasFDerivAt_eq_of_eventually_le_of_eq hle hprofit
    (Real.hasFDerivAt_dotProduct y₀ p₀) hdiff
  intro v
  rw [← heq, Real.dotL_apply]
  exact dotProduct_comm _ _

/-- Uniqueness of the optimal net supply under differentiability of profit:
two profit-maximizing net supplies at `p₀` coincide when `π` is differentiable
at `p₀`. -/
theorem netSupply_unique_of_hasFDerivAt {ι : Type*} [Fintype ι]
    {Y : Set (ι → ℝ)} {π : (ι → ℝ) → ℝ} {p₀ y₀ y₁ : ι → ℝ}
    {π' : (ι → ℝ) →L[ℝ] ℝ}
    (hπ : ∀ᶠ p in 𝓝 p₀, IsLUB ((fun y => p ⬝ᵥ y) '' Y) (π p))
    (hy₀ : y₀ ∈ Y) (hprofit₀ : p₀ ⬝ᵥ y₀ = π p₀)
    (hy₁ : y₁ ∈ Y) (hprofit₁ : p₀ ⬝ᵥ y₁ = π p₀)
    (hdiff : HasFDerivAt π π' p₀) :
    y₀ = y₁ := by
  have h0 := hasFDerivAt_profit_eq_netSupply hπ hy₀ hprofit₀ hdiff
  have h1 := hasFDerivAt_profit_eq_netSupply hπ hy₁ hprofit₁ hdiff
  exact dotProduct_eq _ _ (fun u => by rw [← h0 u, ← h1 u])

/-- Hotelling's lemma in canonical gradient form: the derivative of the profit
function at `p₀` is `Real.dotL y₀`. -/
theorem hasFDerivAt_profit_eq_dotL {ι : Type*} [Fintype ι]
    {Y : Set (ι → ℝ)} {π : (ι → ℝ) → ℝ} {p₀ y₀ : ι → ℝ}
    {π' : (ι → ℝ) →L[ℝ] ℝ}
    (hπ : ∀ᶠ p in 𝓝 p₀, IsLUB ((fun y => p ⬝ᵥ y) '' Y) (π p))
    (hy₀ : y₀ ∈ Y) (hprofit : p₀ ⬝ᵥ y₀ = π p₀)
    (hdiff : HasFDerivAt π π' p₀) :
    π' = Real.dotL y₀ := by
  have h := hasFDerivAt_profit_eq_netSupply hπ hy₀ hprofit hdiff
  apply ContinuousLinearMap.ext
  intro v
  rw [h v, Real.dotL_apply]
  exact dotProduct_comm _ _

end Economics.Producer
