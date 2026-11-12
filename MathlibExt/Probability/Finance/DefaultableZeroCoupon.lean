/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Defaultable zero-coupon bonds

On a finite state space with state prices `ψ`, a fixed-exposure, fixed-recovery
defaultable zero-coupon bond with face `N` pays `R * N` in default states and `N`
otherwise, where `R` is the recovery rate. Its state-price value equals the loss-adjusted
formula `D * N * (1 - q_D * (1 - R))`, where `D = ∑ ω, ψ ω` is the risk-free discount
factor (the price of a unit risk-free payoff) and `q_D` is the state-price mass of the
default states over `D`. For positive state prices `q_D ∈ [0, 1]` and is a genuine
risk-neutral default probability (`riskNeutralDefaultProb_mem_Icc`); for arbitrary `ψ`
the formula is a pure algebraic identity and `q_D` is only a ratio. The state prices are
taken as given (the FTAP in `MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing`
supplies them); this gap does not re-derive them.

## Main results

* `statePriceValue_eq_discountFactor_mul`: the loss-adjusted pricing formula.
* `riskNeutralDefaultProb_mem_Icc`: `q_D ∈ [0, 1]` for positive state prices.

## References

* D. Duffie and K. J. Singleton, *Credit Risk: Pricing, Measurement, and Management*,
  Princeton University Press (2003), Chapter 3.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.DefaultableZeroCoupon

/-- The payoff of the defaultable zero-coupon bond in state `ω`: recovery `R * N` if `ω` is a
default state, the full exposure `N` otherwise. -/
noncomputable def defaultablePayoff (N R : ℝ) {Ω : Type*} (default : Ω → Prop)
    [DecidablePred default] (ω : Ω) : ℝ :=
  if default ω then R * N else N

/-- The risk-free discount factor: the state-price value of a unit payoff in every state,
`∑ ω, ψ ω`. -/
noncomputable def riskFreeDiscountFactor {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ) : ℝ :=
  ∑ ω, ψ ω

/-- The risk-neutral default probability: the state-price mass of the default states divided by
the risk-free discount factor. This is a genuine probability in `[0, 1]` only for positive
state prices (see `riskNeutralDefaultProb_mem_Icc`); for arbitrary `ψ` it is only a ratio. -/
noncomputable def riskNeutralDefaultProb {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ)
    (default : Ω → Prop) [DecidablePred default] : ℝ :=
  (∑ ω ∈ Finset.univ.filter default, ψ ω) / riskFreeDiscountFactor ψ

/-- **Loss-adjusted pricing of a defaultable zero-coupon bond.** The state-price value of the
defaultable payoff equals `D * N * (1 - q_D * (1 - R))`: the risk-free value `D * N` minus
the term `D * N * q_D * (1 - R)`, which is the expected loss when the state prices are
positive and `0 ≤ R ≤ 1` (so that `q_D ∈ [0, 1]` and the loss per unit is nonnegative).
The identity itself holds for every `R`, `N`, and state-price vector with `D ≠ 0`. -/
theorem statePriceValue_eq_discountFactor_mul {Ω : Type*} [Fintype Ω] {ψ : Ω → ℝ}
    {N R : ℝ} {default : Ω → Prop} [DecidablePred default]
    (hD : riskFreeDiscountFactor ψ ≠ 0) :
    ∑ ω, ψ ω * defaultablePayoff N R default ω
      = riskFreeDiscountFactor ψ * N * (1 - riskNeutralDefaultProb ψ default * (1 - R)) := by
  classical
  have hsplit : (∑ ω ∈ Finset.univ.filter default, ψ ω * defaultablePayoff N R default ω)
      + (∑ ω ∈ Finset.univ.filter (fun ω => ¬ default ω),
        ψ ω * defaultablePayoff N R default ω)
      = ∑ ω, ψ ω * defaultablePayoff N R default ω :=
    Finset.sum_filter_add_sum_filter_not Finset.univ default _
  have h1 : (∑ ω ∈ Finset.univ.filter default, ψ ω * defaultablePayoff N R default ω)
      = ∑ ω ∈ Finset.univ.filter default, ψ ω * (R * N) := by
    apply Finset.sum_congr rfl
    intro ω hω
    have hd : default ω := (Finset.mem_filter.mp hω).2
    unfold defaultablePayoff
    simp [hd]
  have h2 : (∑ ω ∈ Finset.univ.filter (fun ω => ¬ default ω),
        ψ ω * defaultablePayoff N R default ω)
      = ∑ ω ∈ Finset.univ.filter (fun ω => ¬ default ω), ψ ω * N := by
    apply Finset.sum_congr rfl
    intro ω hω
    have hd : ¬ default ω := (Finset.mem_filter.mp hω).2
    unfold defaultablePayoff
    simp [hd]
  have h3 : (∑ ω ∈ Finset.univ.filter default, ψ ω * (R * N))
      = (∑ ω ∈ Finset.univ.filter default, ψ ω) * (R * N) :=
    (Finset.sum_mul _ _ _).symm
  have h4 : (∑ ω ∈ Finset.univ.filter (fun ω => ¬ default ω), ψ ω * N)
      = (∑ ω ∈ Finset.univ.filter (fun ω => ¬ default ω), ψ ω) * N :=
    (Finset.sum_mul _ _ _).symm
  have hψsplit : (∑ ω ∈ Finset.univ.filter default, ψ ω)
      + (∑ ω ∈ Finset.univ.filter (fun ω => ¬ default ω), ψ ω)
      = ∑ ω, ψ ω :=
    Finset.sum_filter_add_sum_filter_not Finset.univ default _
  have hND : (∑ ω ∈ Finset.univ.filter (fun ω => ¬ default ω), ψ ω)
      = (∑ ω, ψ ω) - ∑ ω ∈ Finset.univ.filter default, ψ ω := by
    linarith [hψsplit]
  rw [← hsplit, h1, h2, h3, h4, hND]
  unfold riskFreeDiscountFactor at hD
  unfold riskNeutralDefaultProb riskFreeDiscountFactor at ⊢
  field_simp
  ring

/-- The risk-neutral default probability lies in `[0, 1]` for positive state prices. -/
theorem riskNeutralDefaultProb_mem_Icc {Ω : Type*} [Fintype Ω] {ψ : Ω → ℝ}
    {default : Ω → Prop} [DecidablePred default] (hψ : ∀ ω, 0 < ψ ω) :
    riskNeutralDefaultProb ψ default ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  unfold riskNeutralDefaultProb riskFreeDiscountFactor
  constructor
  · apply div_nonneg
    · apply Finset.sum_nonneg
      intro ω _
      exact le_of_lt (hψ ω)
    · apply Finset.sum_nonneg
      intro ω _
      exact le_of_lt (hψ ω)
  · apply div_le_one_of_le₀
    · apply Finset.sum_le_univ_sum_of_nonneg
      intro ω
      exact le_of_lt (hψ ω)
    · apply Finset.sum_nonneg
      intro ω _
      exact le_of_lt (hψ ω)

end MathlibExt.Probability.Finance.DefaultableZeroCoupon
