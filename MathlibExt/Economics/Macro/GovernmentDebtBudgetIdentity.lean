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
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Finite-horizon government budget identity

Debt recursion `B (t + 1) = (1 + r) * B t + D (t + 1)` with primary deficit `D`.
Initial debt plus the present value of primary deficits equals the terminal debt
discounted back to today; the terminal debt is retained explicitly.

## Main results

* `MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity.debt_discounted_step`: discounted step.
* `MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity.governmentBudgetIdentity`: the identity.
* `MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity.governmentBudgetIdentity_terminal`:
  terminal-debt form.
-/

namespace MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity

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

/-- **Finite-horizon government budget identity (MA07.T01).** Iterating the debt
recursion, initial debt plus the present value of primary deficits through horizon `n`
equals the terminal debt discounted back to today; the terminal debt is retained
explicitly and not assumed away:
`B 0 + ∑ s ∈ Finset.Icc 1 n, D s / (1 + r) ^ s = B n / (1 + r) ^ n`.
The sum telescopes via `Finset.sum_range_sub`; this theorem does not reprove telescoping. -/
theorem governmentBudgetIdentity {B D : ℕ → ℝ} {r : ℝ} (h : DebtRecursion B D r)
    (hr : (1 + r) ≠ 0) (n : ℕ) :
    B 0 + ∑ s ∈ Finset.Icc 1 n, D s / (1 + r) ^ s = B n / (1 + r) ^ n := by
  set f : ℕ → ℝ := fun t => B t / (1 + r) ^ t with hf
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hstep : ∀ k, D (k + 1) / (1 + r) ^ (k + 1) = f (k + 1) - f k := by
    intro k
    have hdisc := debt_discounted_step h hr k
    simp only [hf]
    linarith
  have hrewrite : ∑ s ∈ Finset.Icc 1 n, D s / (1 + r) ^ s
      = ∑ k ∈ Finset.range n, (f (k + 1) - f k) := by
    rw [hIcc, Finset.sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    show D (1 + k) / (1 + r) ^ (1 + k) = f (k + 1) - f k
    rw [add_comm (1 : ℕ) k]
    exact hstep k
  rw [hrewrite, Finset.sum_range_sub f n]
  have hf0 : f 0 = B 0 := by simp only [hf, pow_zero, div_one]
  have hfn : f n = B n / (1 + r) ^ n := by simp only [hf]
  rw [hf0, hfn]
  ring

/-- **Terminal-debt form (MA07.T01).** Initial debt equals discounted terminal debt
minus the present value of primary deficits. -/
theorem governmentBudgetIdentity_terminal {B D : ℕ → ℝ} {r : ℝ} (h : DebtRecursion B D r)
    (hr : (1 + r) ≠ 0) (n : ℕ) :
    B 0 = B n / (1 + r) ^ n - ∑ s ∈ Finset.Icc 1 n, D s / (1 + r) ^ s := by
  have hmain := governmentBudgetIdentity h hr n
  linarith

end MathlibExt.Economics.Macro.GovernmentDebtBudgetIdentity
