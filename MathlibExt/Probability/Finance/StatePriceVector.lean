/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.FundedFTAP
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# State-price vectors from the fundamental theorem of asset pricing

Source: Atlas roadmap FI08.T02. The risk-free funding convention is explicit: buying one unit of asset `a`
at price `p a`, financed by borrowing `p a` at gross risk-free return `R`, has net
funded gain `X a ω - R * p a` in state `ω`. The no-arbitrage predicate
`NoFundedArbitrage` is the one defined next to the funded-gains FTAP in
`MathlibExt.Probability.Finance.FundedFTAP`, re-exported here under its original name.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.StatePriceVector

open MathlibExt.Probability.Finance.FundedFTAP

-- The single funded-arbitrage predicate lives in `FundedFTAP`; this alias keeps the
-- name `StatePriceVector.NoFundedArbitrage` for existing statements.
export MathlibExt.Probability.Finance.FundedFTAP (NoFundedArbitrage)

/-- The state-price vector induced by a normalized pricing probability `q` and gross
risk-free return `R`: `ψ ω = q ω / R`. -/
noncomputable def statePriceVector {Ω : Type*} (q : Ω → ℝ) (R : ℝ) : Ω → ℝ :=
  fun ω => q ω / R

/-- **State-price vector and replication pricing (FI08.T02).** Under no arbitrage on
funded gains, `ψ = q / R` is strictly positive, sums to `1 / R`, and prices every
replicated payoff: the `ψ`-value of the payoff `∑ a, h a * X a ω` of portfolio `h`
equals its cost `∑ a, h a * p a`. The pricing probability `q` and its pricing
identity `∑ ω, q ω * X a ω = R * p a` are the ones supplied by `funded_ftap`; they
are not reproved here. -/
theorem exists_statePriceVector_prices_replicated
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {A : Type*} [Fintype A]
    (X : A → Ω → ℝ) (p : A → ℝ) (R : ℝ) (hR : 0 < R)
    (hNA : NoFundedArbitrage X p R) :
    ∃ ψ : Ω → ℝ, (∀ ω : Ω, 0 < ψ ω) ∧ (∑ ω : Ω, ψ ω = 1 / R) ∧
      ∀ h : A → ℝ, ∑ ω : Ω, ψ ω * (∑ a : A, h a * X a ω) = ∑ a : A, h a * p a := by
  have hR' : R ≠ 0 := ne_of_gt hR
  obtain ⟨q, hqpos, hq1, key⟩ := (funded_ftap X p R).mp hNA
  refine ⟨statePriceVector q R, ?_, ?_, ?_⟩
  · intro ω
    change 0 < q ω / R
    exact div_pos (hqpos ω) hR
  · change (∑ ω : Ω, q ω / R) = 1 / R
    rw [← Finset.sum_div, hq1]
  · intro h
    change (∑ ω : Ω, (q ω / R) * (∑ a : A, h a * X a ω)) = ∑ a : A, h a * p a
    calc (∑ ω : Ω, (q ω / R) * (∑ a : A, h a * X a ω))
        = ∑ ω : Ω, ∑ a : A, (q ω / R) * (h a * X a ω) := by
          apply Finset.sum_congr rfl
          intro ω _
          exact Finset.mul_sum _ _ _
      _ = ∑ a : A, ∑ ω : Ω, (q ω / R) * (h a * X a ω) := Finset.sum_comm
      _ = ∑ a : A, h a * p a := by
          apply Finset.sum_congr rfl
          intro a _
          have hfact : (∑ ω : Ω, (q ω / R) * (h a * X a ω))
              = (h a / R) * (∑ ω : Ω, q ω * X a ω) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω _
            ring
          rw [hfact, key a]
          calc (h a / R) * (R * p a) = h a * p a * R / R := by ring
            _ = h a * p a := mul_div_cancel_right₀ _ hR'

end MathlibExt.Probability.Finance.StatePriceVector
