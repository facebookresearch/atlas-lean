/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Accounting.Ledger
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Accounting.Ledger

open MathlibExt.Economics.Accounting

/-- Test chart: cash (asset), loan (liability), owner's capital (equity). -/
def chart3 : Fin 3 → AccountClass :=
  ![AccountClass.asset, AccountClass.liability, AccountClass.equity]

/-- Opening debit-positive balances: cash 100, loan 60 (credit), capital 40 (credit). -/
def opening3 : Fin 3 → ℝ :=
  ![100, -60, -40]

/-- Borrow 50: debit cash 50, credit loan 50. -/
def borrow3 : Fin 3 → ℝ :=
  ![50, -50, 0]

/-- One-sided (unbalanced) entry: debit cash 10 with no credit. -/
def oneSided3 : Fin 3 → ℝ :=
  ![10, 0, 0]

/-- The opening three-account books satisfy the accounting equation. -/
theorem test_opening3 : AccountingEquation chart3 opening3 := by
  rw [accountingEquation_iff_sum_eq_zero]
  norm_num [Fin.sum_univ_three, opening3]

/-- Borrowing 50 (debit cash, credit loan) is a balanced entry. -/
theorem test_borrow3_isBalanced : IsBalanced borrow3 := by
  simp only [IsBalanced]
  norm_num [Fin.sum_univ_three, borrow3]

/-- Posting the balanced borrowing entry keeps the accounting equation, by `accountingEquation_post`. -/
theorem test_borrow3_preserves : AccountingEquation chart3 (post opening3 borrow3) := by
  exact accountingEquation_post test_opening3 test_borrow3_isBalanced

/-- After borrowing: assets 150, liabilities 110, equity 40. -/
theorem test_borrow3_totals :
    assets chart3 (post opening3 borrow3) = 150 ∧
      liabilities chart3 (post opening3 borrow3) = 110 ∧
      equity chart3 (post opening3 borrow3) = 40 := by
  simp only [assets, liabilities, equity, Finset.sum_filter, Fin.sum_univ_three]
  simp [chart3, post, opening3, borrow3]
  norm_num

/-- A one-sided (unbalanced) debit of 10 breaks the accounting equation. -/
theorem test_oneSided3_breaks : ¬ AccountingEquation chart3 (post opening3 oneSided3) := by
  rw [accountingEquation_iff_sum_eq_zero]
  norm_num [Fin.sum_univ_three, post, opening3, oneSided3]

end MathlibExtTest.Economics.Accounting.Ledger
