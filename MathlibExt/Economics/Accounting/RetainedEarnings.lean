/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Accounting.Ledger
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

/-!
# Closing entries and the retained-earnings roll-forward (Atlas AC03.T01)

Each account has a closing role: permanent (including retained earnings) or one of
the temporary revenue, expense and distribution roles. The closing entry zeroes every
temporary account and moves their net balance into the retained-earnings account
(the Income Summary step is collapsed into one entry). It is balanced, so it preserves
the accounting equation by `accountingEquation_post`, and the retained-earnings
balance rolls forward by net income minus distributions.

## Main results

* `MathlibExt.Economics.Accounting.isBalanced_closingEntry`
* `MathlibExt.Economics.Accounting.post_closingEntry_of_ne_permanent`
* `MathlibExt.Economics.Accounting.retainedEarnings_rollForward`
* `MathlibExt.Economics.Accounting.accountingEquation_post_closingEntry`

## References

* OpenStax, *Principles of Accounting, Volume 1: Financial Accounting*, §5.1
  (closing entries).
-/

namespace MathlibExt.Economics.Accounting

/-- Role of an account under the closing convention: permanent (balance-sheet) accounts,
including retained earnings, and the temporary revenue, expense and distribution
(dividend/drawing) accounts that are closed at period end. -/
inductive ClosingRole
  | permanent
  | revenue
  | expense
  | distribution
  deriving DecidableEq

/-- Sum of the debit-positive balances of the accounts with closing role `r`. -/
def roleTotal {α : Type*} [Fintype α] (role : α → ClosingRole) (r : ClosingRole)
    (b : α → ℝ) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => role a = r), b a

/-- Net income for the period: revenues (credit-normal) minus expenses (debit-normal),
read from the pre-closing balances. -/
def netIncome {α : Type*} [Fintype α] (role : α → ClosingRole) (b : α → ℝ) : ℝ :=
  -roleTotal role ClosingRole.revenue b - roleTotal role ClosingRole.expense b

/-- Distributions for the period (debit-normal dividend/drawing accounts). -/
def distributions {α : Type*} [Fintype α] (role : α → ClosingRole) (b : α → ℝ) : ℝ :=
  roleTotal role ClosingRole.distribution b

/-- Closing entry: zero every temporary (non-permanent) account and transfer their net
debit-positive balance to the retained-earnings account `re`. -/
def closingEntry {α : Type*} [Fintype α] [DecidableEq α] (role : α → ClosingRole) (re : α)
    (b : α → ℝ) : α → ℝ :=
  fun a => (if role a = ClosingRole.permanent then 0 else -b a) +
    (if a = re then ∑ t ∈ Finset.univ.filter (fun t => role t ≠ ClosingRole.permanent), b t
      else 0)

/-- The closing entry is balanced: it moves the temporary balances to `re` unchanged in total. -/
theorem isBalanced_closingEntry {α : Type*} [Fintype α] [DecidableEq α]
    (role : α → ClosingRole) (re : α) (b : α → ℝ) :
    IsBalanced (closingEntry role re b) := by
  have hpt : ∀ a : α, (if role a = ClosingRole.permanent then (0:ℝ) else -b a) =
      (if role a ≠ ClosingRole.permanent then -b a else 0) := by
    intro a
    by_cases h : role a = ClosingRole.permanent <;> simp [h, ne_eq]
  have h1 : (∑ a, (if role a = ClosingRole.permanent then (0:ℝ) else -b a)) =
      -(∑ t ∈ Finset.univ.filter (fun t => role t ≠ ClosingRole.permanent), b t) := by
    simp only [hpt, ← Finset.sum_filter, Finset.sum_neg_distrib]
  have h2 : (∑ a, (if a = re then
      (∑ t ∈ Finset.univ.filter (fun t => role t ≠ ClosingRole.permanent), b t) else (0:ℝ))) =
      (∑ t ∈ Finset.univ.filter (fun t => role t ≠ ClosingRole.permanent), b t) := by
    rw [Finset.sum_ite_eq']
    simp
  have hfun : ∀ a : α, closingEntry role re b a =
      (if role a = ClosingRole.permanent then (0:ℝ) else -b a) +
      (if a = re then (∑ t ∈ Finset.univ.filter (fun t => role t ≠ ClosingRole.permanent), b t)
        else 0) := fun a => rfl
  change (∑ a, closingEntry role re b a) = 0
  rw [Finset.sum_congr rfl (fun a _ => hfun a), Finset.sum_add_distrib, h1, h2]
  exact neg_add_cancel _

/-- Closing leaves every temporary account at zero. -/
theorem post_closingEntry_of_ne_permanent {α : Type*} [Fintype α] [DecidableEq α]
    {role : α → ClosingRole} {re : α} (hre : role re = ClosingRole.permanent) (b : α → ℝ)
    {a : α} (ha : role a ≠ ClosingRole.permanent) :
    post b (closingEntry role re b) a = 0 := by
  have hane : a ≠ re := by
    intro h
    subst h
    exact ha hre
  have hfun : post b (closingEntry role re b) a =
      b a + ((if role a = ClosingRole.permanent then (0:ℝ) else -b a) +
        (if a = re then (∑ t ∈ Finset.univ.filter (fun t => role t ≠ ClosingRole.permanent), b t)
          else 0)) := rfl
  rw [hfun, ite_eq_right ha, ite_eq_right hane, add_zero, add_neg_cancel]

/-- Retained-earnings roll-forward: after closing, the (credit-normal) retained-earnings
balance equals the opening retained earnings plus net income minus distributions. -/
theorem retainedEarnings_rollForward {α : Type*} [Fintype α] [DecidableEq α]
    {role : α → ClosingRole} {re : α} (hre : role re = ClosingRole.permanent) (b : α → ℝ) :
    -post b (closingEntry role re b) re = -b re + netIncome role b - distributions role b := by
  have hcase : ∀ a : α, (if role a ≠ ClosingRole.permanent then b a else (0:ℝ)) =
      (if role a = ClosingRole.revenue then b a else 0) +
      (if role a = ClosingRole.expense then b a else 0) +
      (if role a = ClosingRole.distribution then b a else 0) := by
    intro a
    cases role a <;> simp [ne_eq]
  have hS : (∑ t ∈ Finset.univ.filter (fun t => role t ≠ ClosingRole.permanent), b t) =
      (∑ a ∈ Finset.univ.filter (fun a => role a = ClosingRole.revenue), b a) +
      (∑ a ∈ Finset.univ.filter (fun a => role a = ClosingRole.expense), b a) +
      (∑ a ∈ Finset.univ.filter (fun a => role a = ClosingRole.distribution), b a) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => hcase a)
  have hfun : post b (closingEntry role re b) re =
      b re + ((if role re = ClosingRole.permanent then (0:ℝ) else -b re) +
        (if re = re then (∑ t ∈ Finset.univ.filter (fun t => role t ≠ ClosingRole.permanent), b t)
          else 0)) := rfl
  have hNI : netIncome role b =
      -(∑ a ∈ Finset.univ.filter (fun a => role a = ClosingRole.revenue), b a) -
      (∑ a ∈ Finset.univ.filter (fun a => role a = ClosingRole.expense), b a) := rfl
  have hD : distributions role b =
      (∑ a ∈ Finset.univ.filter (fun a => role a = ClosingRole.distribution), b a) := rfl
  rw [hfun, hNI, hD, ite_eq_left hre, ite_eq_left (rfl : re = re), zero_add, hS]
  ring

/-- Closing preserves the accounting equation. -/
theorem accountingEquation_post_closingEntry {α : Type*} [Fintype α] [DecidableEq α]
    {cls : α → AccountClass} {role : α → ClosingRole} {re : α} {b : α → ℝ}
    (hb : AccountingEquation cls b) :
    AccountingEquation cls (post b (closingEntry role re b)) := by
  exact accountingEquation_post hb (isBalanced_closingEntry role re b)

end MathlibExt.Economics.Accounting
