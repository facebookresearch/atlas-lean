/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteProbability
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Real option value

A decision maker with a finite set of feasible actions may wait and choose the best
action after seeing the state. The option value is the expected statewise maximum;
committing in advance to any one feasible action cannot beat it.

Expected values are the canonical finite-state
`MathlibExt.Probability.FiniteProbability.expectation`, `∑ ω, p ω * f ω`. The theorems
below need only nonnegative weights `p`, not `∑ ω, p ω = 1`.

## Main results

* `MathlibExt.Economics.Finance.RealOptionValue.optionValue`: expected statewise
  maximum over actions.
* `MathlibExt.Economics.Finance.RealOptionValue.optionValue_ge_commitment`: the option
  beats any commitment.
* `MathlibExt.Economics.Finance.RealOptionValue.maxCommitment_le_optionValue`: the option
  beats the best commitment.

## References

* H. Raiffa and R. Schlaifer, *Applied Statistical Decision Theory*, Division of Research,
  Graduate School of Business Administration, Harvard University (1961), Chapter 4, Section 5
  (the value of perfect information): choosing the act after the state is known is worth
  `E[max_a V_a]`, and its excess over the best act chosen in advance, `max_a E[V_a]`, is the
  expected value of perfect information, which is nonnegative. This is the comparison proved
  here: `optionValue` is `E[max_a V_a]`, and a commitment to `b` is worth `E[V_b]`.
* A. K. Dixit and R. S. Pindyck, *Investment under Uncertainty*, Princeton University Press
  (1994), Chapter 2: the value of the option to wait and decide after the uncertainty is
  resolved, compared with committing now, in simple two-period examples.

Atlas roadmap target FI13.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.RealOptionValue

open MathlibExt.Probability.FiniteProbability

/-- Value of the option to choose, after seeing the state, the best feasible action: the
expected value of the statewise maximum over `actions`, `E[max_a V_a]` (Raiffa and Schlaifer,
Chapter 4, Section 5). `actions` must be nonempty so the statewise maximum exists. -/
noncomputable def optionValue {α Ω : Type*} [Fintype Ω] (actions : Finset α)
    (hne : actions.Nonempty) (p : Ω → ℝ) (V : α → Ω → ℝ) : ℝ :=
  expectation p (fun ω => actions.sup' hne (fun a => V a ω))

/-- **An optional action beats committing to any one feasible action.** For every feasible
`b`, the expected value of committing to `b` is at most the option value. -/
theorem optionValue_ge_commitment {α Ω : Type*} [Fintype Ω] {actions : Finset α}
    {hne : actions.Nonempty} {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) {V : α → Ω → ℝ}
    {b : α} (hb : b ∈ actions) :
    expectation p (V b) ≤ optionValue actions hne p V := by
  simp only [expectation, optionValue]
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun a => V a ω) hb) (hp ω)

/-- **An optional action beats the best commitment.** The maximum over actions of the
committed expected values is at most the option value. -/
theorem maxCommitment_le_optionValue {α Ω : Type*} [Fintype Ω] {actions : Finset α}
    {hne : actions.Nonempty} {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) {V : α → Ω → ℝ} :
    actions.sup' hne (fun a => expectation p (V a)) ≤
      optionValue actions hne p V := by
  apply Finset.sup'_le
  intro a ha
  exact optionValue_ge_commitment hp ha


end MathlibExt.Economics.Finance.RealOptionValue
