/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Economics.Finance.DatedCashFlow

/-!
# Exact cash-flow matching

The surplus of two cash-flow streams under a common discount curve `D` is
the asset present value minus the liability present value,
`cashFlowSurplus D s a l = presentValue D s a - presentValue D s l`, using
the shared FI01 `presentValue` interface. When the asset and liability flows
agree at every payment date, the surplus is zero for every discount curve
(`cashFlowSurplus_eq_zero_of_matched`); no sign or positivity condition on `D`
is needed.

## Main results

* `MathlibExt.Economics.Finance.CashFlowMatching.cashFlowSurplus_eq_zero_of_matched`

## References

SOA Exam FM syllabus (exact cash-flow matching / dedication). Atlas roadmap
target FI04.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.CashFlowMatching

/-- Surplus of exactly matched cash-flow streams under a common discount curve `D`:
the asset present value minus the liability present value, via the shared
`presentValue` interface. -/
noncomputable def cashFlowSurplus (D : ℕ → ℝ) (s : Finset ℕ) (a l : ℕ → ℝ) : ℝ :=
  presentValue D s a - presentValue D s l

/-- **Exact cash-flow matching immunizes against any common discount curve.** If
asset and liability flows agree at every payment date, the surplus is zero for
every discount curve `D` (no sign or positivity condition on `D` needed). -/
theorem cashFlowSurplus_eq_zero_of_matched {D : ℕ → ℝ} {s : Finset ℕ} {a l : ℕ → ℝ}
    (h : ∀ t ∈ s, a t = l t) : cashFlowSurplus D s a l = 0 := by
  unfold cashFlowSurplus
  have hsum : presentValue D s a = presentValue D s l := by
    unfold presentValue
    apply Finset.sum_congr rfl
    intro t ht
    rw [h t ht]
  rw [hsum, sub_self]

end MathlibExt.Economics.Finance.CashFlowMatching
