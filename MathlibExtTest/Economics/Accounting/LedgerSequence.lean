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

namespace MathlibExtTest.Economics.Accounting.LedgerSequence

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

/-- Posting no entries leaves the books unchanged. -/
theorem test_postAll_nil (b : Fin 3 → ℝ) : postAll b [] = b := by
  simp [postAll, List.foldl_nil]

/-- Posting one entry is `post`. -/
theorem test_postAll_singleton (b e : Fin 3 → ℝ) : postAll b [e] = post b e := by
  simp [postAll, List.foldl_cons, List.foldl_nil]

/-- Two balanced entries keep the accounting equation; cash ends at 130. -/
theorem test_two_entries :
    AccountingEquation chart3 (postAll opening3 [borrow3, ![-20, 20, 0]]) ∧
      assets chart3 (postAll opening3 [borrow3, ![-20, 20, 0]]) = 130 := by
  have hfA : Finset.univ.filter (fun a : Fin 3 => chart3 a = AccountClass.asset) = {0} := by
    decide
  have hfL : Finset.univ.filter (fun a : Fin 3 => chart3 a = AccountClass.liability) = {1} := by
    decide
  have hfE : Finset.univ.filter (fun a : Fin 3 => chart3 a = AccountClass.equity) = {2} := by
    decide
  have h0 : postAll opening3 [borrow3, ![-20, 20, 0]] 0 = 130 := by
    simp only [postAll, post, List.foldl_cons, List.foldl_nil, opening3, borrow3,
      Fin.isValue, Matrix.cons_val]
    norm_num
  have h1 : postAll opening3 [borrow3, ![-20, 20, 0]] 1 = -90 := by
    simp only [postAll, post, List.foldl_cons, List.foldl_nil, opening3, borrow3,
      Fin.isValue, Matrix.cons_val]
    norm_num
  have h2 : postAll opening3 [borrow3, ![-20, 20, 0]] 2 = -40 := by
    simp only [postAll, post, List.foldl_cons, List.foldl_nil, opening3, borrow3,
      Fin.isValue, Matrix.cons_val]
    norm_num
  constructor
  · unfold AccountingEquation assets liabilities equity
    rw [hfA, hfL, hfE, Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton,
      h0, h1, h2]
    norm_num
  · unfold assets
    rw [hfA, Finset.sum_singleton, h0]

/-- An unbalanced entry in the sequence changes the trial-balance total. -/
theorem test_unbalanced_in_sequence :
    ∑ a, postAll opening3 [borrow3, oneSided3] a ≠ ∑ a, opening3 a := by
  simp only [Fin.sum_univ_three]
  simp only [postAll, post, List.foldl_cons, List.foldl_nil, opening3, borrow3, oneSided3,
    Fin.isValue, Matrix.cons_val]
  norm_num

end MathlibExtTest.Economics.Accounting.LedgerSequence
