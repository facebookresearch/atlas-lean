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

/-!
# Loan amortization

A loan `L` at per-period rate `r` is repaid by payments `P (t + 1)` at the ends of periods
`t + 1`; payments need not be level. The outstanding balance follows the amortization
recursion `B₀ = L`, `B_{t+1} = (1 + r) B_t - P (t + 1)`. The principal repaid in period
`t + 1` is the payment minus the interest accrued on the opening balance,
`P (t + 1) - r B_t`.

## Main results

* `MathlibExt.Economics.Finance.principalRepaid_eq`: principal repaid in a period is the drop
  in the outstanding balance.
* `MathlibExt.Economics.Finance.sum_principalRepaid_eq`: if the balance after `n` periods is
  zero, the principal repayments over those periods sum to the initial loan (telescoping,
  `Finset.sum_range_sub'`).

No sign condition on `r`, `L` or the payments is assumed.

## References

SOA Exam FM syllabus (loans and amortization schedules); OpenStax, *Principles of
Finance*. Atlas roadmap target FI01.T05.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance

/-- Outstanding loan balance under the amortization recursion: `B₀ = L` and
`B_{t+1} = (1 + r) B_t - P (t + 1)`, where `P (t + 1)` is the payment at the end of
period `t + 1` and `r` the per-period rate (source clause: "amortization
recursion"). Payments need not be level. -/
noncomputable def loanBalance (r L : ℝ) (P : ℕ → ℝ) : ℕ → ℝ
  | 0 => L
  | t + 1 => (1 + r) * loanBalance r L P t - P (t + 1)

/-- Principal repaid in period `t + 1`: the payment minus the interest `r B_t`
accrued on the opening balance (source clause: "principal repayment"). -/
noncomputable def principalRepaid (r L : ℝ) (P : ℕ → ℝ) (t : ℕ) : ℝ :=
  P (t + 1) - r * loanBalance r L P t

/-- Principal repaid in a period is the drop in the outstanding balance. -/
theorem principalRepaid_eq (r L : ℝ) (P : ℕ → ℝ) (t : ℕ) :
    principalRepaid r L P t = loanBalance r L P t - loanBalance r L P (t + 1) := by
  simp only [principalRepaid, loanBalance]
  ring

/-- If the balance after `n` periods is zero, the principal repayments over those
periods sum to the initial loan (Atlas roadmap FI01.T05). -/
theorem sum_principalRepaid_eq (r L : ℝ) (P : ℕ → ℝ) (n : ℕ)
    (hn : loanBalance r L P n = 0) :
    ∑ t ∈ Finset.range n, principalRepaid r L P t = L := by
  simp only [principalRepaid_eq]
  rw [Finset.sum_range_sub' (fun t => loanBalance r L P t) n]
  simp [loanBalance, hn]

end MathlibExt.Economics.Finance
