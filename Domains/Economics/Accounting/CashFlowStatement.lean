/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Classified cash flows sum to the change in cash (Atlas AC03.T02)

Every transaction of a finite period has a cash effect and exactly one activity class:
operating, investing, financing, or noncash. When noncash transactions carry no cash,
operating plus investing plus financing cash flows equal ending cash minus opening
cash. The proof partitions one finite sum by activity class.

## Main results

* `MathlibExt.Economics.Accounting.operating_add_investing_add_financing`

## References

* OpenStax, *Principles of Accounting, Volume 1: Financial Accounting*, §16.2
  (operating, investing and financing activities).
-/

namespace MathlibExt.Economics.Accounting

/-- Statement-of-cash-flows activity class of a transaction; `noncash` marks transactions
with no cash effect (disclosed separately, e.g. depreciation or debt-for-asset swaps). -/
inductive CashActivity
  | operating
  | investing
  | financing
  | noncash
  deriving DecidableEq

/-- Total cash effect of the transactions classified as activity `k`. -/
def activityTotal {ι : Type*} [Fintype ι] (act : ι → CashActivity) (k : CashActivity)
    (cash : ι → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => act i = k), cash i

/-- Ending cash: opening cash plus the cash effect of every transaction of the period. -/
def endingCash {ι : Type*} [Fintype ι] (opening : ℝ) (cash : ι → ℝ) : ℝ :=
  opening + ∑ i, cash i

/-- When every transaction is classified (as operating, investing, financing or noncash)
and noncash transactions have zero cash effect, operating plus investing plus financing
cash flows equal the change in cash. -/
theorem operating_add_investing_add_financing {ι : Type*} [Fintype ι]
    (act : ι → CashActivity) (cash : ι → ℝ) (opening : ℝ)
    (hnoncash : ∀ i, act i = CashActivity.noncash → cash i = 0) :
    activityTotal act CashActivity.operating cash + activityTotal act CashActivity.investing cash +
        activityTotal act CashActivity.financing cash =
      endingCash opening cash - opening := by
  have hpt : ∀ i, (if act i = CashActivity.operating then cash i else 0) +
      (if act i = CashActivity.investing then cash i else 0) +
      (if act i = CashActivity.financing then cash i else 0) = cash i := by
    intro i
    cases hi : act i
    · simp
    · simp
    · simp
    · have h0 := hnoncash i hi
      simp [h0]
  unfold activityTotal endingCash
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  have h2 := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hpt i)
  rw [h2]
  ring

end MathlibExt.Economics.Accounting
