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
public import MathlibExt.Probability.Finance.LawOfOnePrice
public import MathlibExt.Probability.Finance.OptionPayoffs

/-!
# Modigliani–Miller I: capital-structure irrelevance

In a one-period market without arbitrage, a levered firm whose capital
structure is risky debt (face value `F`) plus equity is worth as much as an
unlevered firm with the same operating payoff `V`: the price of the debt plus the
price of the equity equals the price of the unlevered firm. Equity is a European
call on firm value struck at the face value,
`europeanCallPayoff V F = max (V - F) 0`, so debt plus equity pays
`min V F + max (V - F) 0 = V` in every state, and the law of one price
(`MathlibExt.Probability.Finance.LawOfOnePrice.law_of_one_price_of_no_arbitrage`)
turns this payoff identity into the price identity.

The market has finitely many states and securities, with explicit payoffs `X`
and prices `p`; the hypothesis is no funded arbitrage at a gross risk-free return
`R > 0` (`MathlibExt.Probability.Finance.StatePriceVector.NoFundedArbitrage`).
The debt and equity readings need `0 ≤ V` and a face value `0 ≤ F`; for other
real values the payoffs are the total algebraic extensions `min V F` and
`max (V - F) 0`, and the payoff identity still holds.

`weightedValue ψ X = ∑ ω, ψ ω * X ω` values a payoff with arbitrary real weights
`ψ`. `weightedValue_congr` and `weightedValue_debtPayoff_add_europeanCallPayoff`
are congruence and additivity facts about this linear functional. They hold for
every `ψ`, so they are not a pricing result.

## Main results

* `MathlibExt.Economics.Finance.ModiglianiMiller.debtPayoff_add_europeanCallPayoff`:
  debt plus equity reconstructs the firm.
* `MathlibExt.Economics.Finance.ModiglianiMiller.modiglianiMiller_of_no_arbitrage`:
  Modigliani–Miller I.
* `MathlibExt.Economics.Finance.ModiglianiMiller.weightedValue_congr` and
  `MathlibExt.Economics.Finance.ModiglianiMiller.weightedValue_debtPayoff_add_europeanCallPayoff`:
  congruence and additivity of weighted-sum values.

## References

F. Modigliani and M. H. Miller, "The Cost of Capital, Corporation Finance and
the Theory of Investment", American Economic Review 48(3), 1958, Proposition I.
Atlas roadmap target FI09.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.ModiglianiMiller

open MathlibExt.Probability.Finance.OptionPayoffs (europeanCallPayoff)
open MathlibExt.Probability.Finance.LawOfOnePrice (law_of_one_price_of_no_arbitrage)
open MathlibExt.Probability.Finance.StatePriceVector (NoFundedArbitrage)

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

/-- **Modigliani–Miller I** (Modigliani and Miller 1958, Proposition I). Consider a one-period
market with finitely many states `Ω` and securities `A`, payoffs `X` and prices `p`, with no
funded arbitrage at gross risk-free return `R > 0`. Let security `u` be the unlevered firm, with
operating payoff `V`, and let securities `d` and `e` be the debt (face value `F`) and the equity
of the levered firm. Then the levered firm's value, debt plus equity, equals the price of the
unlevered firm: `p d + p e = p u`. -/
theorem modiglianiMiller_of_no_arbitrage {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {A : Type*} [Fintype A] (X : A → Ω → ℝ) (p : A → ℝ) (R : ℝ) (hR : 0 < R)
    (hNA : NoFundedArbitrage X p R) (V : Ω → ℝ) (F : ℝ) {u d e : A}
    (hu : ∀ ω, X u ω = V ω) (hd : ∀ ω, X d ω = debtPayoff (V ω) F)
    (he : ∀ ω, X e ω = europeanCallPayoff (V ω) F) :
    p d + p e = p u := by
  classical
  have hprice := law_of_one_price_of_no_arbitrage X p R hR hNA
    (h := Pi.single d 1 + Pi.single e 1) (h' := Pi.single u 1) fun ω => by
      simp [add_mul, Finset.sum_add_distrib, Pi.single_apply, hu, hd, he,
        debtPayoff_add_europeanCallPayoff]
  simpa [add_mul, Finset.sum_add_distrib, Pi.single_apply] using hprice

/-- Congruence of `weightedValue`: payoffs that agree in every state have equal weighted value,
for any weights `ψ`. -/
theorem weightedValue_congr {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ) {X Y : Ω → ℝ}
    (h : ∀ ω, X ω = Y ω) : weightedValue ψ X = weightedValue ψ Y := by
  unfold weightedValue
  apply Finset.sum_congr rfl
  intro ω _
  show ψ ω * X ω = ψ ω * Y ω
  rw [h ω]

/-- Weighted-sum additivity for the split of a firm into debt (face `F`) and equity: for any
weights `ψ`, the weighted values of the debt and equity payoffs add up to the weighted value of
the firm payoff `V`. This is linearity of `weightedValue` applied to
`debtPayoff_add_europeanCallPayoff`, not Modigliani–Miller I: valuing every payoff with the same
linear functional builds the additivity in. The price statement is
`modiglianiMiller_of_no_arbitrage`. -/
theorem weightedValue_debtPayoff_add_europeanCallPayoff {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ)
    (V : Ω → ℝ) (F : ℝ) :
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
  exact weightedValue_congr ψ (fun ω => debtPayoff_add_europeanCallPayoff (V ω) F)

end MathlibExt.Economics.Finance.ModiglianiMiller
