/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Probability.Finance.OptionPayoffs

/-!
# Modigliani–Miller I: capital-structure irrelevance

A levered firm whose capital structure is risky debt (face value `F`) plus
equity has the same total value as an unlevered firm with the same operating
payoff `V`: the value of the firm does not depend on how its payoff is split
between debt and equity. Equity is a European call on firm value struck at the
face value, `europeanCallPayoff V F = max (V - F) 0`, so the payoff identity is
`min V F + max (V - F) 0 = V`, and equal payoffs have equal value.

Values are weighted sums `∑ ω, ψ ω * X ω` over a finite state space with
arbitrary real weights `ψ`: no positivity, normalization, nonempty state space,
or no-arbitrage condition is assumed, and every identity here holds for all
`ψ`. Reading the weights as state prices, such as the strictly positive vector
that `MathlibExt.Probability.Finance.StatePriceVector.exists_statePriceVector_prices_replicated`
supplies under no arbitrage, is the economic interpretation, not a hypothesis.
That interpretation also needs `0 ≤ V` and a face value `0 ≤ F`; for other real
values the payoffs are the total algebraic extensions `min V F` and
`max (V - F) 0`, and the identities still hold.

## Main results

* `MathlibExt.Economics.Finance.ModiglianiMiller.debtPayoff_add_europeanCallPayoff`:
  debt plus equity reconstructs the firm.
* `MathlibExt.Economics.Finance.ModiglianiMiller.lawOfOnePrice`: equal payoffs
  have equal weighted value.
* `MathlibExt.Economics.Finance.ModiglianiMiller.modiglianiMiller_value`:
  Modigliani–Miller I.

## References

F. Modigliani and M. H. Miller, "The Cost of Capital, Corporation Finance and
the Theory of Investment", American Economic Review 48(3), 1958. Atlas roadmap
target FI09.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.ModiglianiMiller

open MathlibExt.Probability.Finance.OptionPayoffs (europeanCallPayoff)

/-- Weighted-sum value `∑ ω, ψ ω * X ω` of a state-contingent payoff `X` under arbitrary real
weights `ψ`. No positivity or normalization of `ψ` is assumed; reading `ψ` as a state-price
vector is an interpretation, not a hypothesis. -/
noncomputable def weightedValue {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω, ψ ω * X ω

/-- Risky-debt payoff `min V F` at terminal firm value `V` and face value `F`: debt holders are
paid in full when the firm can pay, and take the whole firm otherwise. This reading needs
`0 ≤ V` and `0 ≤ F`; for other real arguments `min V F` is the total algebraic extension, and
the payoff identity below holds for all real `V` and `F`. -/
noncomputable def debtPayoff (V F : ℝ) : ℝ :=
  min V F

/-- Debt plus equity reconstructs the firm: `min V F + max (V - F) 0 = V`. Equity is the
European call `europeanCallPayoff V F` on firm value struck at the face value (limited
liability). Specialization of `min_add_max` and `max_sub_sub_right`; the kernel is not
reproved. -/
theorem debtPayoff_add_europeanCallPayoff (V F : ℝ) :
    debtPayoff V F + europeanCallPayoff V F = V := by
  have hmax := max_sub_sub_right V F F
  rw [sub_self] at hmax
  unfold debtPayoff europeanCallPayoff
  rw [hmax, ← add_sub_assoc, min_add_max, add_sub_cancel_right]

/-- Equal payoffs in every state have equal weighted value, for any weights `ψ`. This is the
pricing step of the law of one price and needs no positivity of `ψ`; the portfolio form under
no arbitrage is
`MathlibExt.Probability.Finance.LawOfOnePrice.law_of_one_price_of_no_arbitrage`. -/
theorem lawOfOnePrice {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ) {X Y : Ω → ℝ}
    (h : ∀ ω, X ω = Y ω) : weightedValue ψ X = weightedValue ψ Y := by
  unfold weightedValue
  apply Finset.sum_congr rfl
  intro ω _
  show ψ ω * X ω = ψ ω * Y ω
  rw [h ω]

/-- **Modigliani–Miller I.** A levered firm whose capital structure is risky debt (face `F`)
plus equity (a European call on firm value struck at `F`) has the same total value as an
unlevered firm with the same operating payoff `V`: for any weights `ψ`, the weighted value of
the whole firm does not depend on how its payoff is split between debt and equity. -/
theorem modiglianiMiller_value {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ) (V : Ω → ℝ)
    (F : ℝ) :
    weightedValue ψ (fun ω => debtPayoff (V ω) F) +
      weightedValue ψ (fun ω => europeanCallPayoff (V ω) F) =
      weightedValue ψ V := by
  have hadd : weightedValue ψ (fun ω => debtPayoff (V ω) F) +
      weightedValue ψ (fun ω => europeanCallPayoff (V ω) F) =
      weightedValue ψ (fun ω => debtPayoff (V ω) F + europeanCallPayoff (V ω) F) := by
    change (∑ ω, ψ ω * debtPayoff (V ω) F) + (∑ ω, ψ ω * europeanCallPayoff (V ω) F) =
      ∑ ω, ψ ω * (debtPayoff (V ω) F + europeanCallPayoff (V ω) F)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    change ψ ω * debtPayoff (V ω) F + ψ ω * europeanCallPayoff (V ω) F =
      ψ ω * (debtPayoff (V ω) F + europeanCallPayoff (V ω) F)
    rw [mul_add]
  rw [hadd]
  exact lawOfOnePrice ψ (fun ω => debtPayoff_add_europeanCallPayoff (V ω) F)

end MathlibExt.Economics.Finance.ModiglianiMiller
