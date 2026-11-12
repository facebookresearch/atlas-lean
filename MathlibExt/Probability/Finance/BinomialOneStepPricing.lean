/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.BinomialReplication
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# One-step binomial pricing equals replication cost

For a one-step claim paying `Cu` in the up state and `Cd` in the down state, the
risk-neutral price `(q * Cu + (1 - q) * Cd) / R` with `q = (R - d) / (u - d)` equals
the replication cost `Δ * S₀ + B`, where `Δ = (Cu - Cd) / ((u - d) * S₀)` is the delta
hedge and `B = (u * Cd - d * Cu) / ((u - d) * R)` is the bond holding. In the landed
binomial model (`BinomialReplication`), the backward-induction value at horizon `1` is
that price and that cost, and the landed delta-hedging ratio at horizon `1` is `Δ`.

## Main results

* `riskNeutralPrice`, `deltaHedge`, `bondHolding`, `replicationCost`: the one-step
  pricing and replication quantities.
* `riskNeutralPrice_eq_replicationCost`: the `q` price equals replication cost.
* `claimValue_one_eq_riskNeutralPrice`, `claimValue_one_eq_replicationCost`: the
  landed backward-induction value at horizon `1` is the price and the cost.
* `hedgeRatio_one_eq_deltaHedge`: the landed delta-hedging ratio at horizon `1` is `Δ`.

## References

* J. C. Cox, S. A. Ross, M. Rubinstein, *Option pricing: a simplified approach*,
  J. Financial Economics 7 (1979), 229–263.
* S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*,
  Springer (2004), Chapter 1.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.BinomialOneStepPricing

open MathlibExt.Probability.Finance.BinomialReplication

/-- One-step risk-neutral price of a claim paying `Cu` in the up state and `Cd` in the down
state, with risk-neutral up probability `q = (R - d) / (u - d)` (source clause: "the one-step
`q` price"). -/
noncomputable def riskNeutralPrice (u d R Cu Cd : ℝ) : ℝ :=
  (rnProb u d R * Cu + (1 - rnProb u d R) * Cd) / R

/-- The delta hedge of the one-step claim: the share holding `Δ = (Cu - Cd) / ((u - d) * S₀)`
that makes the portfolio payoff match the claim in both states (assuming `S₀ ≠ 0`,
`u ≠ d`, `R ≠ 0`). -/
noncomputable def deltaHedge (S₀ u d Cu Cd : ℝ) : ℝ :=
  (Cu - Cd) / ((u - d) * S₀)

/-- The bond holding of the one-step replicating portfolio:
`B = (u * Cd - d * Cu) / ((u - d) * R)`, so that (assuming `S₀ ≠ 0`, `u ≠ d`, `R ≠ 0`)
`Δ * (u * S₀) + B * R = Cu` and `Δ * (d * S₀) + B * R = Cd`. -/
noncomputable def bondHolding (u d R Cu Cd : ℝ) : ℝ :=
  (u * Cd - d * Cu) / ((u - d) * R)

/-- Replication cost of the one-step claim: the initial capital `Δ * S₀ + B` of the
delta-and-bond replicating portfolio. -/
noncomputable def replicationCost (S₀ u d R Cu Cd : ℝ) : ℝ :=
  deltaHedge S₀ u d Cu Cd * S₀ + bondHolding u d R Cu Cd

/-- **The one-step `q` price equals replication cost** (Atlas roadmap FI12.T02, algebra half).
Pure algebra: `field_simp` with `u ≠ d`, `R ≠ 0`, `S₀ ≠ 0`, then `ring`. -/
theorem riskNeutralPrice_eq_replicationCost {S₀ u d R Cu Cd : ℝ} (hS₀ : S₀ ≠ 0)
    (hud : u ≠ d) (hR : R ≠ 0) :
    riskNeutralPrice u d R Cu Cd = replicationCost S₀ u d R Cu Cd := by
  have hud' : u - d ≠ 0 := sub_ne_zero.mpr hud
  unfold riskNeutralPrice replicationCost deltaHedge bondHolding rnProb
  field_simp
  ring

/-- The landed backward-induction value at horizon `1` is the one-step `q` price: unfold
`claimValue` once (`claimValue ... 0 s = V s`) and rewrite with the payoff hypotheses. -/
theorem claimValue_one_eq_riskNeutralPrice {u d R : ℝ} {V : List Bool → ℝ} {Cu Cd : ℝ}
    (hCu : V [true] = Cu) (hCd : V [false] = Cd) :
    claimValue u d R V 1 [] = riskNeutralPrice u d R Cu Cd := by
  change claimValue u d R V (0 + 1) [] = _
  simp only [claimValue, riskNeutralPrice]
  rw [hCu, hCd]

/-- **The one-step `q` price equals replication cost** (Atlas roadmap FI12.T02, in the landed
model): the backward-induction value at horizon `1` is the replication cost. Follows from
the two theorems above. -/
theorem claimValue_one_eq_replicationCost {S₀ u d R : ℝ} {V : List Bool → ℝ} {Cu Cd : ℝ}
    (hS₀ : S₀ ≠ 0) (hud : u ≠ d) (hR : R ≠ 0) (hCu : V [true] = Cu) (hCd : V [false] = Cd) :
    claimValue u d R V 1 [] = replicationCost S₀ u d R Cu Cd := by
  rw [claimValue_one_eq_riskNeutralPrice hCu hCd]
  exact riskNeutralPrice_eq_replicationCost hS₀ hud hR

/-- The landed delta-hedging ratio at horizon `1` is the one-step delta hedge: unfold
`hedgeRatio` (the `claimValue ... 0` terms are the payoffs, the `price` terms are
`u * S₀` and `d * S₀`) and use `u * S₀ - d * S₀ = (u - d) * S₀`. No nonvanishing
hypothesis is needed: both sides are the same quotient. -/
theorem hedgeRatio_one_eq_deltaHedge {S₀ u d R : ℝ} {V : List Bool → ℝ} {Cu Cd : ℝ}
    (hCu : V [true] = Cu) (hCd : V [false] = Cd) :
    hedgeRatio S₀ u d R V 1 [] = deltaHedge S₀ u d Cu Cd := by
  have hlen : (1 : ℕ) - ([] : List Bool).length - 1 = 0 := by decide
  unfold hedgeRatio deltaHedge
  rw [hlen]
  simp only [claimValue, price]
  rw [hCu, hCd]
  have hsub : u * S₀ - d * S₀ = (u - d) * S₀ := by ring
  rw [hsub]

end MathlibExt.Probability.Finance.BinomialOneStepPricing
