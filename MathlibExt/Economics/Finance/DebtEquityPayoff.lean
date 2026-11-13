/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.OptionPayoffs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Tactic.Linarith

/-!
# Debt and equity payoffs

A firm with terminal value `V` and debt face value `F` pays debtholders `min V F` and
equity holders the European call payoff on the firm value with strike `F`,
`europeanCallPayoff V F = max (V - F) 0`; the two payoffs sum to `V`. The identity
holds for every real `V`, so the source's nonnegativity of `V` (limited liability) is
not needed for it; it is retained where it matters, in the nonnegativity of the debt
payoff. Both payoffs are nonnegative when `V, F ≥ 0`; the call (equity) payoff is
nonnegative for all inputs by the canonical
`MathlibExt.Probability.Finance.OptionPayoffs.europeanCallPayoff_nonneg`.

Equity as a call on firm value is the Merton insight; the call payoff itself is the
canonical `MathlibExt.Probability.Finance.OptionPayoffs.europeanCallPayoff`, reused
here rather than redefined.

## Main results

* `debtPayoff_add_europeanCallPayoff`: the balance-sheet identity.
* `debtPayoff_nonneg`: nonnegativity of the debt payoff.

## References

* R. C. Merton, *On the pricing of corporate debt: the risk structure of interest rates*,
  Journal of Finance 29 (1974), 449--470.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.DebtEquityPayoff


/-- The debt payoff at maturity: debtholders receive the firm value or the face value,
whichever is smaller. -/
noncomputable def debtPayoff (V F : ℝ) : ℝ :=
  min V F

/-- **Balance-sheet identity.** Debt plus equity equals the firm value:
`min V F + max (V - F) 0 = V`, with equity as the European call payoff
`europeanCallPayoff V F`. -/
theorem debtPayoff_add_europeanCallPayoff (V F : ℝ) :
    debtPayoff V F
      + MathlibExt.Probability.Finance.OptionPayoffs.europeanCallPayoff V F = V := by
  unfold debtPayoff MathlibExt.Probability.Finance.OptionPayoffs.europeanCallPayoff
  have hmax : max (V - F) 0 = max V F - F := by
    have h := max_sub_sub_right V F F
    rw [sub_self] at h
    exact h
  have hminmax : min V F + max V F = V + F := min_add_max V F
  rw [hmax]
  linarith

/-- The debt payoff is nonnegative for nonnegative firm value and face value. -/
theorem debtPayoff_nonneg {V F : ℝ} (hV : 0 ≤ V) (hF : 0 ≤ F) :
    0 ≤ debtPayoff V F := by
  unfold debtPayoff
  exact le_min hV hF


end MathlibExt.Economics.Finance.DebtEquityPayoff
