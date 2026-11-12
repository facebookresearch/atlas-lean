/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Ricardian tax-timing invariance, two periods

In a finite two-period model with frictionless lump-sum taxes, two tax paths
that both finance the same government spending path at the same rate leave
the household present-value budget unchanged. The government present-value
budget (present value of taxes equals present value of spending) is the
key step. No unrestricted Ricardian equivalence is claimed: the result holds
only in this finite model, with lump-sum taxes, no borrowing constraints,
the same spending path, and the same interest rate.

## Main results

* `MathlibExt.Economics.Macro.RicardianTwoPeriod.government_presentValue_budget`:
  period budgets imply present value of taxes equals present value of spending.
* `MathlibExt.Economics.Macro.RicardianTwoPeriod.taxTimingShift_presentValue_invariant`:
  the household present-value budget is unchanged by a tax-timing shift.

## References

Atlas roadmap target MA07.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.RicardianTwoPeriod

/-- **Government present-value budget (two periods).** With period budgets
`g0 = t0 + b0` (date 0: spending is met by taxes plus new debt) and
`g1 + (1+r) * b0 = t1` (date 1: spending plus debt repayment is met by taxes,
terminal debt zero), the present value of taxes equals the present value of
spending: `t0 + t1/(1+r) = g0 + g1/(1+r)`. -/
theorem government_presentValue_budget {r g0 g1 t0 t1 b0 : ℝ} (h1r : 1 + r ≠ 0)
    (h0 : g0 = t0 + b0) (h1 : g1 + (1 + r) * b0 = t1) :
    t0 + t1 / (1 + r) = g0 + g1 / (1 + r) := by
  have h1' : t1 = g1 + (1 + r) * b0 := h1.symm
  have hdiv : t1 / (1 + r) = g1 / (1 + r) + b0 := by
    rw [h1']
    field_simp
  rw [hdiv, h0]
  ring

/-- **Ricardian tax-timing invariance, two-period finite model (MA07.T04).**
In a finite two-period model with frictionless lump-sum taxes, if two tax paths
`(t0, t1)` and `(t0', t1')` both finance the SAME government spending path
`(g0, g1)` at the same rate `r` (each with its own debt path, terminal debt
zero), then the household present-value budget — after-tax income
`(y0 - t0) + (y1 - t1)/(1+r)` — is unchanged by the tax-timing shift.
No unrestricted Ricardian equivalence is claimed: the statement is only for
this finite model, with lump-sum taxes, no borrowing constraints, the same
spending path, and the same interest rate. -/
theorem taxTimingShift_presentValue_invariant
    {r g0 g1 t0 t1 t0' t1' b0 b0' y0 y1 : ℝ} (h1r : 1 + r ≠ 0)
    (h0 : g0 = t0 + b0) (h1 : g1 + (1 + r) * b0 = t1)
    (h0' : g0 = t0' + b0') (h1' : g1 + (1 + r) * b0' = t1') :
    (y0 - t0) + (y1 - t1) / (1 + r) = (y0 - t0') + (y1 - t1') / (1 + r) := by
  have e1 := government_presentValue_budget h1r h0 h1
  have e2 := government_presentValue_budget h1r h0' h1'
  field_simp at e1 e2 ⊢
  linear_combination e2 - e1

end MathlibExt.Economics.Macro.RicardianTwoPeriod
