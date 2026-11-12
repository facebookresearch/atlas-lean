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

/-!
# Modigliani–Miller I: capital-structure irrelevance

A levered firm whose capital structure is risky debt (face value `F`) plus
equity has the same total value as an unlevered firm with the same operating
payoff `V`, under state-price valuation: the value of the firm does not depend
on how its payoff is split between debt and equity. The payoff identity is
`min V F + max (V - F) 0 = V`; equal payoffs have equal value (law of one
price). The state-price vector is taken as a hypothesis: its existence under
no arbitrage is the fundamental theorem of asset pricing, cited, not reproved.

## Main results

* `MathlibExt.Economics.Finance.ModiglianiMiller.debtPayoff_add_equityPayoff`:
  debt plus equity reconstructs the firm.
* `MathlibExt.Economics.Finance.ModiglianiMiller.lawOfOnePrice`: equal payoffs
  have equal state-price value (local form of roadmap FI08.T04; future
  unification with FI08.T04).
* `MathlibExt.Economics.Finance.ModiglianiMiller.modiglianiMiller_value`:
  Modigliani–Miller I.

## References

F. Modigliani and M. H. Miller, "The Cost of Capital, Corporation Finance and
the Theory of Investment", American Economic Review 48(3), 1958. Atlas roadmap
target FI09.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.ModiglianiMiller

/-- State-price value of a state-contingent payoff `X` under state prices `ψ`: the
linear pricing functional whose existence under no arbitrage is the FTAP conclusion
(cited, not reproved here). This is a local copy of the one-line functional; the
forward-market file `ForwardCostOfCarry` carries its own copy for the same
functional, and the two may be unified in the future. -/
noncomputable def statePriceValue {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω, ψ ω * X ω

/-- Risky-debt payoff at terminal firm value `V` and face value `F`: debt holders are
paid in full when the firm can pay, and take the whole firm otherwise. The economic
reading assumes `V ≥ 0`; the payoff identity below holds for all real `V`. -/
noncomputable def debtPayoff (V F : ℝ) : ℝ :=
  min V F

/-- Equity payoff at terminal firm value `V` and face value `F`: the residual claim
after debt is paid, floored at zero (limited liability). -/
noncomputable def equityPayoff (V F : ℝ) : ℝ :=
  max (V - F) 0

/-- Debt plus equity reconstructs the firm: `min V F + max (V - F) 0 = V`.
Specialization of `min_add_max` and `max_sub_sub_right`; the kernel is not reproved. -/
theorem debtPayoff_add_equityPayoff (V F : ℝ) :
    debtPayoff V F + equityPayoff V F = V := by
  have hmax := max_sub_sub_right V F F
  rw [sub_self] at hmax
  unfold debtPayoff equityPayoff
  rw [hmax, ← add_sub_assoc, min_add_max, add_sub_cancel_right]

/-- Law of one price for state-price valuation: equal payoffs in every state have
equal value. This is the local form of roadmap FI08.T04 (unmerged, Lane 4, same run),
stated here so this file is self-contained; future unification with FI08.T04. -/
theorem lawOfOnePrice {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ) {X Y : Ω → ℝ}
    (h : ∀ ω, X ω = Y ω) : statePriceValue ψ X = statePriceValue ψ Y := by
  unfold statePriceValue
  apply Finset.sum_congr rfl
  intro ω _
  show ψ ω * X ω = ψ ω * Y ω
  rw [h ω]

/-- **Modigliani–Miller I.** A levered firm whose capital structure is risky debt
(face `F`) plus equity has the same total value as an unlevered firm with the same
operating payoff `V`, under state-price valuation: the value of the whole firm does
not depend on how its payoff is split between debt and equity. -/
theorem modiglianiMiller_value {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ) (V : Ω → ℝ)
    (F : ℝ) :
    statePriceValue ψ (fun ω => debtPayoff (V ω) F) +
      statePriceValue ψ (fun ω => equityPayoff (V ω) F) =
      statePriceValue ψ V := by
  have hadd : statePriceValue ψ (fun ω => debtPayoff (V ω) F) +
      statePriceValue ψ (fun ω => equityPayoff (V ω) F) =
      statePriceValue ψ (fun ω => debtPayoff (V ω) F + equityPayoff (V ω) F) := by
    show (∑ ω, ψ ω * debtPayoff (V ω) F) + (∑ ω, ψ ω * equityPayoff (V ω) F) =
      ∑ ω, ψ ω * (debtPayoff (V ω) F + equityPayoff (V ω) F)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    show ψ ω * debtPayoff (V ω) F + ψ ω * equityPayoff (V ω) F =
      ψ ω * (debtPayoff (V ω) F + equityPayoff (V ω) F)
    rw [mul_add]
  rw [hadd]
  exact lawOfOnePrice ψ (fun ω => debtPayoff_add_equityPayoff (V ω) F)

end MathlibExt.Economics.Finance.ModiglianiMiller
