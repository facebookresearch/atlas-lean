/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.ExchangeEquilibriumExistence

@[expose] public section

/-!
# Walras' law for exchange economies (Atlas EC15.T01)

Source: J. Levin, *General Equilibrium*, Stanford Econ 202 lecture notes (2006), Definition 4
(excess demand `zⁱ(p) = xⁱ(p, p · eⁱ) - eⁱ`, `z(p) = ∑ zⁱ(p)`) and Proposition 4(iii) (Walras'
law `p · z(p) = 0`). Walras' law is an accounting identity: if every consumer's demand exhausts
the consumer's budget, `p · xⁱ(p) = p · eⁱ`, the value of aggregate excess demand is zero,
whether or not markets clear. It is stated for Atlas's demand-form exchange economy
`ExchangeEquilibriumExistence.ExchangeEconomy` and its `excessDemand` (Atlas
`MathlibExt/Economics/ExchangeEquilibriumExistence.lean`, where the same identity appears only
inside the existence proof). Budget exhaustion is a hypothesis; for utility-maximizing demand it
follows from local nonsatiation (EC02.T02).
-/

namespace MathlibExt.Economics.ExchangeEquilibriumExistence.ExchangeEconomy

/-- Walras' law (Levin, *General Equilibrium*, Proposition 4(iii)): if every consumer's demand at
prices `p` exhausts the consumer's budget, the value of aggregate excess demand at `p` is zero. -/
theorem dotProduct_excessDemand_eq_zero {I L : Type*} [Fintype I] [Fintype L]
    (E : ExchangeEconomy I L) {p : L → ℝ}
    (hbudget : ∀ i, p ⬝ᵥ E.demand i p = p ⬝ᵥ E.endowment i) : p ⬝ᵥ E.excessDemand p = 0 := by
  unfold excessDemand
  rw [dotProduct_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [dotProduct_sub, hbudget i, sub_self]

end MathlibExt.Economics.ExchangeEquilibriumExistence.ExchangeEconomy
