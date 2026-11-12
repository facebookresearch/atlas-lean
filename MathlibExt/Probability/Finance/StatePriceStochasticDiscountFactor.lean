/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# State prices and the stochastic discount factor

On a finite state space, a positive state-price vector `ψ` and full-support physical
probabilities `P` induce the stochastic discount factor `m ω = ψ ω / P ω`, and the
state-price value of a payoff equals its `P`-expectation under `m`:
`∑ ω, P ω * (m ω * X ω) = ∑ ω, ψ ω * X ω`.

This is the state-price-to-SDF direction. It is distinct from the marginal-utility SDF
pricing equation in `MathlibExt.Probability.Finance.ConsumptionSDF`, which derives an SDF
from an investor's first-order condition; here the state prices are taken as given.

## Main results

* `stochasticDiscountFactor_pos`: the induced SDF is positive.
* `price_eq_physicalExpectation_stochasticDiscountFactor`: state-price value equals
  `E_P[m * X]`.

## References

* J. H. Cochrane, *Asset Pricing*, revised edition, Princeton University Press (2005),
  Section 1.2.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.StatePriceStochasticDiscountFactor

/-- The stochastic discount factor induced by the state-price vector `ψ` and the physical
probabilities `P`: `m ω = ψ ω / P ω`. Requires `P ω ≠ 0` to be meaningful; the theorems below
assume `0 < P ω`. -/
noncomputable def stochasticDiscountFactor {Ω : Type*} (ψ P : Ω → ℝ) (ω : Ω) : ℝ :=
  ψ ω / P ω

/-- The state-price value of the payoff `X`: `∑ ω, ψ ω * X ω`. -/
noncomputable def statePriceValue {Ω : Type*} [Fintype Ω] (ψ : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω, ψ ω * X ω

/-- The `P`-expectation of `Y`: `∑ ω, P ω * Y ω`. -/
noncomputable def physicalExpectation {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Y : Ω → ℝ) : ℝ :=
  ∑ ω, P ω * Y ω

/-- A positive state-price vector and full-support physical probabilities induce a positive
stochastic discount factor. -/
theorem stochasticDiscountFactor_pos {Ω : Type*} {ψ P : Ω → ℝ}
    (hψ : ∀ ω, 0 < ψ ω) (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    0 < stochasticDiscountFactor ψ P ω := by
  unfold stochasticDiscountFactor
  exact div_pos (hψ ω) (hP ω)

/-- **State-price value equals SDF pricing.** With full-support physical probabilities, the
state-price value of a payoff equals its `P`-expectation under the induced stochastic discount
factor: `E_P[m * X] = ∑ ω, ψ ω * X ω`. -/
theorem price_eq_physicalExpectation_stochasticDiscountFactor {Ω : Type*} [Fintype Ω]
    {ψ P X : Ω → ℝ} (hP : ∀ ω, 0 < P ω) :
    physicalExpectation P (fun ω => stochasticDiscountFactor ψ P ω * X ω)
      = statePriceValue ψ X := by
  unfold physicalExpectation statePriceValue stochasticDiscountFactor
  apply Finset.sum_congr rfl
  intro ω _
  have hPω : P ω ≠ 0 := ne_of_gt (hP ω)
  calc P ω * (ψ ω / P ω * X ω)
      = P ω * (ψ ω / P ω) * X ω := by ring
    _ = ψ ω * X ω := by rw [mul_div_cancel₀ _ hPω]

end MathlibExt.Probability.Finance.StatePriceStochasticDiscountFactor
