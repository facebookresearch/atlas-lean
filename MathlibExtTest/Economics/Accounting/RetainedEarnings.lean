/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Accounting.RetainedEarnings
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Accounting.RetainedEarnings

open MathlibExt.Economics.Accounting

/-- Test chart: cash (asset), retained earnings, sales revenue, wage expense, dividends
(all equity). -/
def chart5 : Fin 5 → AccountClass :=
  ![AccountClass.asset, AccountClass.equity, AccountClass.equity, AccountClass.equity,
    AccountClass.equity]

/-- Closing roles for `chart5`; account `1` is retained earnings. -/
def role5 : Fin 5 → ClosingRole :=
  ![ClosingRole.permanent, ClosingRole.permanent, ClosingRole.revenue, ClosingRole.expense,
    ClosingRole.distribution]

/-- Pre-closing balances: cash 70, retained earnings 50 (credit), revenue 40 (credit),
expense 15, dividends 5. -/
def preClosing5 : Fin 5 → ℝ :=
  ![70, -50, -40, 15, 5]

/-- Net income of the five-account example: revenue 40 minus expense 15. -/
theorem test_netIncome5 : netIncome role5 preClosing5 = 25 := by
  have hrev : Finset.univ.filter (fun a : Fin 5 => role5 a = ClosingRole.revenue) = {2} := by
    decide
  have hexp : Finset.univ.filter (fun a : Fin 5 => role5 a = ClosingRole.expense) = {3} := by
    decide
  have h2 : preClosing5 2 = (-40 : ℝ) := rfl
  have h3 : preClosing5 3 = (15 : ℝ) := rfl
  have hNI : netIncome role5 preClosing5 =
      -(∑ a ∈ Finset.univ.filter (fun a => role5 a = ClosingRole.revenue), preClosing5 a) -
      (∑ a ∈ Finset.univ.filter (fun a => role5 a = ClosingRole.expense), preClosing5 a) := rfl
  rw [hNI, hrev, hexp, Finset.sum_singleton, Finset.sum_singleton, h2, h3]
  norm_num

/-- Distributions of the five-account example: dividends 5. -/
theorem test_distributions5 : distributions role5 preClosing5 = 5 := by
  have hdist : Finset.univ.filter (fun a : Fin 5 => role5 a = ClosingRole.distribution) = {4} := by
    decide
  have h4 : preClosing5 4 = (5 : ℝ) := rfl
  have hD : distributions role5 preClosing5 =
      (∑ a ∈ Finset.univ.filter (fun a => role5 a = ClosingRole.distribution), preClosing5 a) := rfl
  rw [hD, hdist, Finset.sum_singleton, h4]

/-- Retained earnings roll forward from 50 to 50 + 25 - 5 = 70. -/
theorem test_rollForward5 : -post preClosing5 (closingEntry role5 1 preClosing5) 1 = 70 := by
  have hre : role5 1 = ClosingRole.permanent := rfl
  have h := retainedEarnings_rollForward hre preClosing5
  rw [test_netIncome5, test_distributions5] at h
  have h1 : preClosing5 1 = (-50 : ℝ) := rfl
  rw [h1] at h
  linarith

/-- The closed five-account books satisfy the accounting equation. -/
theorem test_closed5 :
    AccountingEquation chart5 (post preClosing5 (closingEntry role5 1 preClosing5)) := by
  have hb : AccountingEquation chart5 preClosing5 := by
    have hasset : Finset.univ.filter (fun a : Fin 5 => chart5 a = AccountClass.asset) = {0} := by
      decide
    have hliab : Finset.univ.filter (fun a : Fin 5 => chart5 a = AccountClass.liability) =
        (∅ : Finset (Fin 5)) := by
      decide
    have heq : Finset.univ.filter (fun a : Fin 5 => chart5 a = AccountClass.equity) =
        {1, 2, 3, 4} := by
      decide
    have h0 : preClosing5 0 = (70 : ℝ) := rfl
    have h1 : preClosing5 1 = (-50 : ℝ) := rfl
    have h2 : preClosing5 2 = (-40 : ℝ) := rfl
    have h3 : preClosing5 3 = (15 : ℝ) := rfl
    have h4 : preClosing5 4 = (5 : ℝ) := rfl
    have hAE : AccountingEquation chart5 preClosing5 ↔
        (∑ a ∈ Finset.univ.filter (fun a => chart5 a = AccountClass.asset), preClosing5 a) =
        -(∑ a ∈ Finset.univ.filter (fun a => chart5 a = AccountClass.liability), preClosing5 a) +
        -(∑ a ∈ Finset.univ.filter (fun a => chart5 a = AccountClass.equity), preClosing5 a) :=
      Iff.rfl
    rw [hAE, hasset, hliab, heq, Finset.sum_singleton, Finset.sum_empty,
      Finset.sum_insert (show (1 : Fin 5) ∉ ({2, 3, 4} : Finset (Fin 5)) by decide),
      Finset.sum_insert (show (2 : Fin 5) ∉ ({3, 4} : Finset (Fin 5)) by decide),
      Finset.sum_insert (show (3 : Fin 5) ∉ ({4} : Finset (Fin 5)) by decide),
      Finset.sum_singleton, h0, h1, h2, h3, h4]
    norm_num
  exact accountingEquation_post_closingEntry (role := role5) (re := 1) hb

end MathlibExtTest.Economics.Accounting.RetainedEarnings
