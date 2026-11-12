/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# State-price vectors from the fundamental theorem of asset pricing

See the contract `/tmp/atlas-econ-50b/lane4/FI08.T02-contract.md` for the source and
clause map. The risk-free funding convention is explicit: buying one unit of asset `a`
at price `p a`, financed by borrowing `p a` at gross risk-free return `R`, has net
funded gain `X a ω - R * p a` in state `ω`.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.StatePriceVector

open MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing

/-- No arbitrage on funded gains: no portfolio `h` has nonnegative funded gain in
every state and strictly positive funded gain in some state. The funded gain of
buying `h a` units of asset `a` at price `p a`, financed at gross risk-free
return `R`, is `h a * (X a ω - R * p a)` in state `ω`. -/
def NoFundedArbitrage {Ω : Type*} [Fintype Ω] {A : Type*} [Fintype A]
    (X : A → Ω → ℝ) (p : A → ℝ) (R : ℝ) : Prop :=
  ¬ ∃ h : A → ℝ, (∀ ω : Ω, 0 ≤ ∑ a : A, h a * (X a ω - R * p a)) ∧
    (∃ ω : Ω, 0 < ∑ a : A, h a * (X a ω - R * p a))

/-- The state-price vector induced by a normalized pricing probability `q` and gross
risk-free return `R`: `ψ ω = q ω / R`. -/
noncomputable def statePriceVector {Ω : Type*} (q : Ω → ℝ) (R : ℝ) : Ω → ℝ :=
  fun ω => q ω / R

/-- **State-price vector and replication pricing (FI08.T02).** Under no arbitrage on
funded gains, `ψ = q / R` is strictly positive, sums to `1 / R`, and prices every
replicated payoff: the `ψ`-value of the payoff `∑ a, h a * X a ω` of portfolio `h`
equals its cost `∑ a, h a * p a`. The pricing probability `q` is the one supplied
by `one_period_fundamental_theorem_asset_pricing_general` applied to the funded
gains; it is not reproved here. -/
theorem exists_statePriceVector_prices_replicated
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {A : Type*} [Fintype A]
    (X : A → Ω → ℝ) (p : A → ℝ) (R : ℝ) (hR : 0 < R)
    (hNA : NoFundedArbitrage X p R) :
    ∃ ψ : Ω → ℝ, (∀ ω : Ω, 0 < ψ ω) ∧ (∑ ω : Ω, ψ ω = 1 / R) ∧
      ∀ h : A → ℝ, ∑ ω : Ω, ψ ω * (∑ a : A, h a * X a ω) = ∑ a : A, h a * p a := by
  have hR' : R ≠ 0 := ne_of_gt hR
  have hNA' : ¬ ∃ h : A → ℝ, (∀ ω : Ω, 0 ≤ ∑ a : A, h a * (X a ω - R * p a)) ∧
      (∃ ω : Ω, 0 < ∑ a : A, h a * (X a ω - R * p a)) := hNA
  obtain ⟨q, hqpos, hq1, hqg⟩ :=
    (one_period_fundamental_theorem_asset_pricing_general
      (fun a ω => X a ω - R * p a)).mp hNA'
  refine ⟨statePriceVector q R, ?_, ?_, ?_⟩
  · intro ω
    change 0 < q ω / R
    exact div_pos (hqpos ω) hR
  · change (∑ ω : Ω, q ω / R) = 1 / R
    rw [← Finset.sum_div, hq1]
  · intro h
    change (∑ ω : Ω, (q ω / R) * (∑ a : A, h a * X a ω)) = ∑ a : A, h a * p a
    have key : ∀ a : A, ∑ ω : Ω, q ω * X a ω = R * p a := by
      intro a
      have h0 : ∑ ω : Ω, q ω * (X a ω - R * p a) = 0 := hqg a
      have hfactor : (∑ ω : Ω, q ω * (R * p a)) = (R * p a) * (∑ ω : Ω, q ω) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        ring
      have hexp : (∑ ω : Ω, q ω * (X a ω - R * p a))
          = (∑ ω : Ω, q ω * X a ω) - R * p a := by
        have h1 : (∑ ω : Ω, q ω * (X a ω - R * p a))
            = ∑ ω : Ω, (q ω * X a ω - q ω * (R * p a)) :=
          Finset.sum_congr rfl (fun ω _ => mul_sub _ _ _)
        rw [h1, Finset.sum_sub_distrib, hfactor, hq1, mul_one]
      have hsub : (∑ ω : Ω, q ω * X a ω) - R * p a = 0 := by
        rw [← hexp]
        exact h0
      exact sub_eq_zero.mp hsub
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
