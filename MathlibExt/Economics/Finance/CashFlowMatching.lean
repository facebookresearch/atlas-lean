/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Exact cash-flow matching

The surplus of two cash-flow streams under a common discount curve `D` is
`cashFlowSurplus D s a l = ∑ t ∈ s, D t * (a t - l t)`. When the asset and
liability flows agree at every payment date, the surplus is zero for every
discount curve (`cashFlowSurplus_eq_zero_of_matched`); no sign or positivity
condition on `D` is needed. Future unification: with the FI01 `presentValue`,
this surplus equals `presentValue D s a - presentValue D s l`.

## Main results

* `MathlibExt.Economics.Finance.CashFlowMatching.cashFlowSurplus_eq_zero_of_matched`

## References

SOA Exam FM syllabus (exact cash-flow matching / dedication). Atlas roadmap
target FI04.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.CashFlowMatching

/-- Surplus of exactly matched cash-flow streams under a common discount curve `D`:
the discounted asset flows minus the discounted liability flows, as one sum of
per-date differences. -/
noncomputable def cashFlowSurplus (D : ℕ → ℝ) (s : Finset ℕ) (a l : ℕ → ℝ) : ℝ :=
  ∑ t ∈ s, D t * (a t - l t)

/-- **Exact cash-flow matching immunizes against any common discount curve.** If
asset and liability flows agree at every payment date, the surplus is zero for
every discount curve `D` (no sign or positivity condition on `D` needed). -/
theorem cashFlowSurplus_eq_zero_of_matched {D : ℕ → ℝ} {s : Finset ℕ} {a l : ℕ → ℝ}
    (h : ∀ t ∈ s, a t = l t) : cashFlowSurplus D s a l = 0 := by
  unfold cashFlowSurplus
  have hmul : ∀ t ∈ s, D t * (a t - l t) = D t * a t - D t * l t := fun t _ => mul_sub _ _ _
  rw [Finset.sum_congr rfl hmul, Finset.sum_sub_distrib]
  have hsum : (∑ t ∈ s, D t * a t) = ∑ t ∈ s, D t * l t := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [h t ht]
  rw [hsum, sub_self]

end MathlibExt.Economics.Finance.CashFlowMatching
