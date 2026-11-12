/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Forward cost of carry by replication

Replicating a forward with borrowing and the underlying yields the frozen
cost-of-carry price `F = (S0 - inc / R) * R`, where `S0` is the spot price, `R`
the gross riskless rate, and `inc` the known terminal income on one unit of the
underlying. Cash-and-carry (long one underlying, borrow `S0`) has terminal
payoff `(S ω + inc) - S0 * R`; state-price valuation of the underlying, the
forward (zero entry cost), and the riskless unit then forces the price.

## Main results

* `MathlibExt.Economics.Finance.ForwardCostOfCarry.forward_replication_payoff`:
  the cash-and-carry replication identity.
* `MathlibExt.Economics.Finance.ForwardCostOfCarry.forward_cost_of_carry`:
  the cost-of-carry price from the three pricing equations.

Related landed result: `MathlibExt.Probability.Finance.ForwardPriceBounds`
proves the same frictionless price by collapsing a no-arbitrage interval; this
file proves it by the distinct replication + state-price (law-of-one-price)
route. The state-price vector is taken as a hypothesis: its existence under no
arbitrage is the fundamental theorem of asset pricing, cited, not reproved.

## References

J. C. Hull, *Options, Futures, and Other Derivatives*, Chapter 5 (forward
prices, cost of carry). Atlas roadmap target FI10.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.ForwardCostOfCarry

/-- State-price value of a state-contingent payoff `X` under state prices `ψ`: the
linear pricing functional whose existence under no arbitrage is the FTAP conclusion
(cited, not reproved here). Only its pricing equations are used below; positivity
of `ψ` is not needed for these identities. This is a local copy of the one-line
functional; the Modigliani–Miller file carries its own copy, and the two may be
unified in the future. -/
noncomputable def statePriceValue {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω, ψ ω * X ω

/-- Replication identity: cash-and-carry (long one unit of the underlying, which pays
terminal spot `S ω` plus known terminal income `inc`, and borrow `S0` at gross rate
`R`) has terminal payoff `(S ω + inc) - S0 * R`, which equals the long-forward payoff
`S ω - F` when `F = S0 * R - inc`. -/
theorem forward_replication_payoff {Ω : Type*} {S : Ω → ℝ} {S0 R inc F : ℝ}
    (hF : F = S0 * R - inc) (ω : Ω) :
    (S ω + inc) - S0 * R = S ω - F := by
  rw [hF]
  ring

/-- **Forward cost of carry.** Replicating a forward with borrowing and the underlying
yields the frozen cost-of-carry price: if state prices `ψ` price the riskless unit
payoff at `1 / R`, price the underlying (spot plus known terminal income `inc`) at `S0`,
and price the forward (payoff `S ω - F`, zero entry cost) at `0`, then
`F = (S0 - inc / R) * R`, i.e. the spot price less the present value of the income,
grossed up at `R`.
Related landed result: `MathlibExt.Probability.Finance.ForwardPriceBounds`
proves the same frictionless price by collapsing a no-arbitrage interval; this
theorem proves it by the distinct replication + state-price (law-of-one-price)
route of roadmap FI10.T01. -/
theorem forward_cost_of_carry {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ) {S : Ω → ℝ}
    {S0 R inc F : ℝ} (hR : R ≠ 0) (hψ : ∑ ω, ψ ω = 1 / R)
    (hunderlying : statePriceValue ψ (fun ω => S ω + inc) = S0)
    (hforward : statePriceValue ψ (fun ω => S ω - F) = 0) :
    F = (S0 - inc / R) * R := by
  simp only [statePriceValue] at hunderlying hforward
  simp only [mul_add] at hunderlying
  simp only [mul_sub] at hforward
  rw [Finset.sum_add_distrib] at hunderlying
  rw [Finset.sum_sub_distrib] at hforward
  have hinc : ∑ ω, ψ ω * inc = (1 / R) * inc := by
    rw [← Finset.sum_mul, hψ]
  have hFsum : ∑ ω, ψ ω * F = (1 / R) * F := by
    rw [← Finset.sum_mul, hψ]
  rw [hinc] at hunderlying
  rw [hFsum] at hforward
  have hS : ∑ ω, ψ ω * S ω = (1 / R) * F := by
    exact sub_eq_zero.mp hforward
  rw [hS] at hunderlying
  have hmul : R * ((1 / R) * F + (1 / R) * inc) = F + inc := by
    field_simp
  have h2 : R * ((1 / R) * F + (1 / R) * inc) = R * S0 := by
    rw [hunderlying]
  have h3 : F + inc = R * S0 := by
    rw [hmul] at h2
    exact h2
  have hgoal : (S0 - inc / R) * R = R * S0 - inc := by
    field_simp
  calc F = (F + inc) - inc := by ring
    _ = R * S0 - inc := by rw [h3]
    _ = (S0 - inc / R) * R := by rw [hgoal]

end MathlibExt.Economics.Finance.ForwardCostOfCarry
