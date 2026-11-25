/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Double-entry ledgers and the accounting equation (Atlas AC01.T01)

A finite chart of accounts `α` carries debit-positive signed balances `b : α → ℝ`
(credit balances are negative) and a balance-sheet classification
`cls : α → AccountClass`. A journal entry is a vector of signed postings; it is
balanced when debits equal credits, i.e. its postings sum to zero. Total assets are
the sum of asset balances; liabilities and equity are minus the sums of their
credit-normal balances.

Posting a balanced entry leaves the trial-balance total unchanged; the accounting
equation `assets = liabilities + equity` is equivalent to a zero trial balance; hence
a balanced entry preserves the accounting equation. The proofs specialize
`Finset.sum_add_distrib` and the filter partition of a finite sum.

## Main results

* `MathlibExt.Economics.Accounting.sum_post_of_isBalanced`
* `MathlibExt.Economics.Accounting.accountingEquation_iff_sum_eq_zero`
* `MathlibExt.Economics.Accounting.accountingEquation_post`

## References

* OpenStax, *Principles of Accounting, Volume 1: Financial Accounting*, §3.2 (the
  accounting equation) and §3.5 (journal entries; debits equal credits).
-/

namespace MathlibExt.Economics.Accounting

/-- Balance-sheet class of an account in a finite chart of accounts: asset, liability, or
equity. Temporary revenue, expense and distribution accounts are equity subaccounts. -/
inductive AccountClass
  | asset
  | liability
  | equity
  deriving DecidableEq

/-- A journal entry `e : α → ℝ` over the chart `α`, written as signed postings in the
debit-positive convention (a debit of `x` to account `a` is `e a = x`, a credit is
`e a = -x`), is balanced when total debits equal total credits, i.e. the postings sum
to zero. -/
def IsBalanced {α : Type*} [Fintype α] (e : α → ℝ) : Prop :=
  ∑ a, e a = 0

/-- Post the journal entry `e` to the debit-positive ledger balances `b`. -/
def post {α : Type*} (b e : α → ℝ) : α → ℝ :=
  fun a => b a + e a

/-- Total assets: the sum of the debit-positive balances of the asset accounts. -/
def assets {α : Type*} [Fintype α] (cls : α → AccountClass) (b : α → ℝ) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => cls a = AccountClass.asset), b a

/-- Total liabilities: liability accounts are credit-normal, so this is minus the sum of
their debit-positive balances. -/
def liabilities {α : Type*} [Fintype α] (cls : α → AccountClass) (b : α → ℝ) : ℝ :=
  -∑ a ∈ Finset.univ.filter (fun a => cls a = AccountClass.liability), b a

/-- Total equity: equity accounts are credit-normal, so this is minus the sum of their
debit-positive balances. -/
def equity {α : Type*} [Fintype α] (cls : α → AccountClass) (b : α → ℝ) : ℝ :=
  -∑ a ∈ Finset.univ.filter (fun a => cls a = AccountClass.equity), b a

/-- The accounting equation `assets = liabilities + equity` for the ledger balances `b`
under the classification `cls`. -/
def AccountingEquation {α : Type*} [Fintype α] (cls : α → AccountClass) (b : α → ℝ) :
    Prop :=
  assets cls b = liabilities cls b + equity cls b

/-- Posting a balanced journal entry leaves the trial-balance total (the sum of all
debit-positive balances) unchanged. -/
theorem sum_post_of_isBalanced {α : Type*} [Fintype α] {e : α → ℝ} (he : IsBalanced e)
    (b : α → ℝ) :
    ∑ a, post b e a = ∑ a, b a := by
  simp only [post, IsBalanced] at he ⊢
  rw [Finset.sum_add_distrib, he, add_zero]

/-- The accounting equation holds exactly when the trial balance is zero (total debits
equal total credits), for every classification of the accounts. -/
theorem accountingEquation_iff_sum_eq_zero {α : Type*} [Fintype α]
    (cls : α → AccountClass) (b : α → ℝ) :
    AccountingEquation cls b ↔ ∑ a, b a = 0 := by
  have h1 : (∑ a ∈ Finset.univ.filter (fun a => cls a = AccountClass.asset), b a) +
      (∑ a ∈ Finset.univ.filter (fun a => ¬cls a = AccountClass.asset), b a) =
      ∑ a, b a :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have h2 : (∑ a ∈ (Finset.univ.filter (fun a => ¬cls a = AccountClass.asset)).filter
      (fun a => cls a = AccountClass.liability), b a) +
      (∑ a ∈ (Finset.univ.filter (fun a => ¬cls a = AccountClass.asset)).filter
      (fun a => ¬cls a = AccountClass.liability), b a) =
      ∑ a ∈ Finset.univ.filter (fun a => ¬cls a = AccountClass.asset), b a :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hf1 : (Finset.univ.filter (fun a => ¬cls a = AccountClass.asset)).filter
      (fun a => cls a = AccountClass.liability) =
      Finset.univ.filter (fun a => cls a = AccountClass.liability) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      decide
  have hf2 : (Finset.univ.filter (fun a => ¬cls a = AccountClass.asset)).filter
      (fun a => ¬cls a = AccountClass.liability) =
      Finset.univ.filter (fun a => cls a = AccountClass.equity) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hna, hnl⟩
      cases h : cls x <;> simp_all
    · intro h
      rw [h]
      exact ⟨by decide, by decide⟩
  rw [hf1, hf2] at h2
  simp only [AccountingEquation, assets, liabilities, equity]
  constructor <;> intro h <;> linarith

/-- A balanced journal entry preserves the accounting equation. -/
theorem accountingEquation_post {α : Type*} [Fintype α] {cls : α → AccountClass}
    {b e : α → ℝ} (hb : AccountingEquation cls b) (he : IsBalanced e) :
    AccountingEquation cls (post b e) := by
  rw [accountingEquation_iff_sum_eq_zero] at hb ⊢
  exact (sum_post_of_isBalanced he b).trans hb

end MathlibExt.Economics.Accounting
