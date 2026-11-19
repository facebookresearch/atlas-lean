/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Accounting.LedgerSequence
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Balanced books need not be correct books (Atlas AC01.T03)

A trial balance only detects entries whose debits and credits differ. On a worked
four-account chart (cash, equipment, loan, capital/expense):

* omitting a balanced borrowing entry leaves books that still satisfy the accounting
  equation but differ from the books of what happened;
* recording an equipment purchase as an expense is a balanced entry that keeps the
  accounting equation, yet reports total assets 70 instead of 100;

so "books built from balanced entries are correct" is false.

## Main results

* `MathlibExt.Economics.Accounting.omission_counterexample`
* `MathlibExt.Economics.Accounting.misclassification_counterexample`
* `MathlibExt.Economics.Accounting.not_forall_balanced_books_correct`

## References

* OpenStax, *Principles of Accounting, Volume 1: Financial Accounting*, §3.6 (the
  trial balance reveals computational errors when it does not balance).
-/

namespace MathlibExt.Economics.Accounting

/-- Worked chart: cash (asset), equipment (asset), loan (liability), owner's
capital/expense (equity). -/
def exampleChart : Fin 4 → AccountClass :=
  ![AccountClass.asset, AccountClass.asset, AccountClass.liability, AccountClass.equity]

/-- Opening balances: cash 100, equipment 0, loan 60 (credit), capital 40 (credit). -/
def exampleOpening : Fin 4 → ℝ :=
  ![100, 0, -60, -40]

/-- The transaction that happened: borrow 50 (debit cash, credit loan). -/
def exampleBorrow : Fin 4 → ℝ :=
  ![50, 0, -50, 0]

/-- The transaction that happened: buy equipment for 30 cash (debit equipment, credit cash). -/
def exampleEquipmentPurchase : Fin 4 → ℝ :=
  ![-30, 30, 0, 0]

/-- Misclassified record of the equipment purchase: debited to the equity (expense)
account instead of equipment. -/
def exampleExpensed : Fin 4 → ℝ :=
  ![-30, 0, 0, 30]

private theorem ac01t03_filter_asset : Finset.univ.filter
    (fun a => exampleChart a = AccountClass.asset) = ({0, 1} : Finset (Fin 4)) := by
  decide

private theorem ac01t03_filter_liability : Finset.univ.filter
    (fun a => exampleChart a = AccountClass.liability) = ({2} : Finset (Fin 4)) := by
  decide

private theorem ac01t03_filter_equity : Finset.univ.filter
    (fun a => exampleChart a = AccountClass.equity) = ({3} : Finset (Fin 4)) := by
  decide

private theorem ac01t03_mem01 : (0 : Fin 4) ∉ ({1} : Finset (Fin 4)) := by
  decide

private theorem ac01t03_borrow_balanced : IsBalanced exampleBorrow := by
  change ∑ a, exampleBorrow a = 0
  rw [Fin.sum_univ_four]
  simp [exampleBorrow]

private theorem ac01t03_expensed_balanced : IsBalanced exampleExpensed := by
  change ∑ a, exampleExpensed a = 0
  rw [Fin.sum_univ_four]
  simp [exampleExpensed]

private theorem ac01t03_opening_equation :
    AccountingEquation exampleChart exampleOpening := by
  simp only [AccountingEquation, assets, liabilities, equity, ac01t03_filter_asset,
    ac01t03_filter_liability, ac01t03_filter_equity]
  rw [Finset.sum_insert ac01t03_mem01, Finset.sum_singleton, Finset.sum_singleton,
    Finset.sum_singleton]
  norm_num [exampleOpening]

/-- Omission: dropping the balanced borrowing entry leaves books that satisfy the
accounting equation but differ from the books of what happened. -/
theorem omission_counterexample :
    AccountingEquation exampleChart (postAll exampleOpening []) ∧
      postAll exampleOpening [] ≠ postAll exampleOpening [exampleBorrow] := by
  constructor
  · exact ac01t03_opening_equation
  · intro h
    have h0 := congrFun h 0
    norm_num [postAll, post, exampleOpening, exampleBorrow] at h0

/-- Misclassification: recording the equipment purchase as an expense is balanced and
keeps the accounting equation, yet reports total assets 70 instead of 100. -/
theorem misclassification_counterexample :
    IsBalanced exampleExpensed ∧
      AccountingEquation exampleChart (postAll exampleOpening [exampleExpensed]) ∧
      assets exampleChart (postAll exampleOpening [exampleExpensed]) = 70 ∧
      assets exampleChart (postAll exampleOpening [exampleEquipmentPurchase]) = 100 := by
  have hes : ∀ e ∈ [exampleExpensed], IsBalanced e := by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ac01t03_expensed_balanced
  refine ⟨ac01t03_expensed_balanced,
    accountingEquation_postAll ac01t03_opening_equation hes, ?_, ?_⟩
  · simp only [assets, ac01t03_filter_asset]
    rw [Finset.sum_insert ac01t03_mem01, Finset.sum_singleton]
    norm_num [postAll, post, exampleOpening, exampleExpensed]
  · simp only [assets, ac01t03_filter_asset]
    rw [Finset.sum_insert ac01t03_mem01, Finset.sum_singleton]
    norm_num [postAll, post, exampleOpening, exampleEquipmentPurchase]

/-- "Balanced books imply correct books" is false: books built only from balanced entries,
starting from books that satisfy the accounting equation, need not equal the books of
the transactions that actually occurred. -/
theorem not_forall_balanced_books_correct :
    ¬ ∀ (α : Type) [Fintype α] (cls : α → AccountClass) (b : α → ℝ)
        (actual recorded : List (α → ℝ)),
        AccountingEquation cls b → (∀ e ∈ actual, IsBalanced e) →
          (∀ e ∈ recorded, IsBalanced e) → postAll b recorded = postAll b actual := by
  intro H
  obtain ⟨hb, hne⟩ := omission_counterexample
  have h1 : ∀ e ∈ [exampleBorrow], IsBalanced e := by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ac01t03_borrow_balanced
  have h2 : ∀ e ∈ ([] : List (Fin 4 → ℝ)), IsBalanced e :=
    fun e he => absurd he (by simp)
  have heq := H (Fin 4) exampleChart exampleOpening [exampleBorrow] [] hb h1 h2
  exact hne heq

end MathlibExt.Economics.Accounting
