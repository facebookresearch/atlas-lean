/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Tactic.NormNum

/-!
# European option payoffs

European call and put payoffs at expiry, and the identity that call payoff
minus put payoff equals terminal underlying minus strike.

## Main results

* `callPayoff_sub_putPayoff`: `(S - K)⁺ - (K - S)⁺ = S - K`, from
  `posPart_sub_negPart`.
* `callPayoff_sub_putPayoff_example`: a concrete instance.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.OptionPayoffs

/-- European call payoff at expiry: `max (S - K) 0`, where `S` is the terminal
underlying price and `K` is the strike. -/
noncomputable def europeanCallPayoff (S K : ℝ) : ℝ := max (S - K) 0

/-- European put payoff at expiry: `max (K - S) 0`, where `S` is the terminal
underlying price and `K` is the strike. -/
noncomputable def europeanPutPayoff (S K : ℝ) : ℝ := max (K - S) 0

/-- Call payoff minus put payoff equals terminal underlying minus strike:
`(S - K)⁺ - (K - S)⁺ = S - K`. This is `posPart_sub_negPart` once
`max (K - S) 0` is rewritten as the negative part of `S - K`; do not reprove
the Mathlib lemma. -/
theorem callPayoff_sub_putPayoff (S K : ℝ) :
    europeanCallPayoff S K - europeanPutPayoff S K = S - K := by
  have hcall : max (S - K) 0 = (S - K)⁺ := by rw [posPart_def]
  have hput : max (K - S) 0 = (S - K)⁻ := by rw [negPart_def, neg_sub]
  unfold europeanCallPayoff europeanPutPayoff
  rw [hcall, hput, posPart_sub_negPart]

/-- Concrete instance: `S = 110`, `K = 100`: call payoff `10`, put payoff `0`,
difference `10 = 110 - 100`. -/
theorem callPayoff_sub_putPayoff_example :
    europeanCallPayoff 110 100 - europeanPutPayoff 110 100 = 10 := by
  rw [callPayoff_sub_putPayoff]
  norm_num

end MathlibExt.Probability.Finance.OptionPayoffs
