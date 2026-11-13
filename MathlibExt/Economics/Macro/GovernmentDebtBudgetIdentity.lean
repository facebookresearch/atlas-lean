/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Economics.Finance.DatedCashFlow
import MathlibExt.Economics.Finance.FiniteDividendDiscount
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Finite-horizon government budget identity

Debt recursion `B (t + 1) = (1 + r) * B t + D (t + 1)` with primary deficit `D`.
Initial debt plus the present value of primary deficits equals the terminal debt
discounted back to today; the terminal debt is retained explicitly. The identity is stated
canonically with the shared `MathlibExt.Economics.Finance.presentValue` and
`discountFactor` API; the raw division forms are derived compatibility lemmas.

## Main results

* `MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity.debt_discounted_step`: discounted step.
* `MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity.governmentBudgetIdentity_presentValue`:
  the identity,
  `B 0 + presentValue (discountFactor r) (Finset.Icc 1 n) D = discountFactor r n * B n`.
* `MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity.governmentBudgetIdentity`: the identity
  in raw division form.
* `MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity.governmentBudgetIdentity_terminal`:
  terminal-debt form.

## References

* O. Blanchard, *Macroeconomics*, 4th edition, Chapter 26 ("Fiscal Policy: A Summing Up"),
  section "The Government Budget Constraint": in real terms,
  `B_t = (1 + r) B_{t-1} + (G_t - T_t)`, where `G_t - T_t` is the primary deficit of year
  `t`. `DebtRecursion` is this recursion with the index shifted by one: `D (t + 1)` is the
  primary deficit of period `t + 1`.

Atlas roadmap target MA07.T01.
-/

namespace MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity

open MathlibExt.Economics.Finance

/-- Government debt recursion: next period's debt is this period's debt with interest
plus next period's primary deficit, `B (t + 1) = (1 + r) * B t + D (t + 1)`.
`D t` is the primary deficit at date `t` (government spending minus taxes, excluding
interest); a primary surplus is a negative `D t`. -/
def DebtRecursion (B D : ℕ → ℝ) (r : ℝ) : Prop :=
  ∀ t, B (t + 1) = (1 + r) * B t + D (t + 1)

/-- **Discounted debt step (MA07.T01).** Dividing the recursion by `(1 + r) ^ (t + 1)`
gives the telescoping step: discounted debt rises by the discounted primary deficit. -/
theorem debt_discounted_step {B D : ℕ → ℝ} {r : ℝ} (h : DebtRecursion B D r)
    (hr : (1 + r) ≠ 0) (t : ℕ) :
    B (t + 1) / (1 + r) ^ (t + 1) = B t / (1 + r) ^ t + D (t + 1) / (1 + r) ^ (t + 1) := by
  have hpow1 : (1 + r) ^ t ≠ 0 := pow_ne_zero _ hr
  have hpow2 : (1 + r) ^ (t + 1) ≠ 0 := pow_ne_zero _ hr
  rw [h t, pow_succ]
  field_simp

/-- **Finite-horizon government budget identity (MA07.T01), present-value form.** Iterating
the debt recursion, initial debt plus the present value of primary deficits through horizon
`n` equals the discounted terminal debt; the terminal debt is retained explicitly and not
assumed away:
`B 0 + presentValue (discountFactor r) (Finset.Icc 1 n) D = discountFactor r n * B n`.
Rewritten as `B t = (-D (t + 1) + B (t + 1)) / (1 + r)`, the debt recursion is the price
recursion of `FiniteDividendDiscount.finiteDividendDiscount` with cash flow `-D`; the
identity is that theorem plus `presentValue_smul`. -/
theorem governmentBudgetIdentity_presentValue {B D : ℕ → ℝ} {r : ℝ} (h : DebtRecursion B D r)
    (hr : (1 + r) ≠ 0) (n : ℕ) :
    B 0 + presentValue (discountFactor r) (Finset.Icc 1 n) D = discountFactor r n * B n := by
  have hrec : ∀ t, B t = ((-D) (t + 1) + B (t + 1)) / (1 + r) := by
    intro t
    rw [Pi.neg_apply, h t]
    field_simp
    ring
  have hdd := FiniteDividendDiscount.finiteDividendDiscount hr hrec n
  have hneg : presentValue (discountFactor r) (Finset.Icc 1 n) (-D)
      = -presentValue (discountFactor r) (Finset.Icc 1 n) D := by
    have hD : -D = (-1 : ℝ) • D := by
      funext t
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul]
    rw [hD, presentValue_smul, neg_one_mul]
  rw [hneg] at hdd
  linarith

/-- **Finite-horizon government budget identity (MA07.T01), raw division form.** The
present-value identity `governmentBudgetIdentity_presentValue` with the discount factors
written as divisions:
`B 0 + ∑ s ∈ Finset.Icc 1 n, D s / (1 + r) ^ s = B n / (1 + r) ^ n`. -/
theorem governmentBudgetIdentity {B D : ℕ → ℝ} {r : ℝ} (h : DebtRecursion B D r)
    (hr : (1 + r) ≠ 0) (n : ℕ) :
    B 0 + ∑ s ∈ Finset.Icc 1 n, D s / (1 + r) ^ s = B n / (1 + r) ^ n := by
  simpa only [presentValue, discountFactor, inv_mul_eq_div] using
    governmentBudgetIdentity_presentValue h hr n

/-- **Terminal-debt form (MA07.T01).** Initial debt equals discounted terminal debt
minus the present value of primary deficits. -/
theorem governmentBudgetIdentity_terminal {B D : ℕ → ℝ} {r : ℝ} (h : DebtRecursion B D r)
    (hr : (1 + r) ≠ 0) (n : ℕ) :
    B 0 = B n / (1 + r) ^ n - ∑ s ∈ Finset.Icc 1 n, D s / (1 + r) ^ s := by
  have hmain := governmentBudgetIdentity h hr n
  linarith

end MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity
