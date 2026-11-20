/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Accounting.CashFlowStatement
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

@[expose] public section

namespace MathlibExtTest.Economics.Accounting.CashFlowStatement

open MathlibExt.Economics.Accounting

/-- Test classification: cash sale, equipment purchase, loan proceeds, depreciation. -/
def act4 : Fin 4 → CashActivity :=
  ![CashActivity.operating, CashActivity.investing, CashActivity.financing,
    CashActivity.noncash]

/-- Cash effects: sale +100, equipment -40, loan +30, depreciation 0. -/
def cash4 : Fin 4 → ℝ :=
  ![100, -40, 30, 0]

/-- Operating 100, investing -40, financing 30, ending cash 110 from opening 20. -/
theorem test_cashFlow4 :
    activityTotal act4 CashActivity.operating cash4 = 100 ∧
      activityTotal act4 CashActivity.investing cash4 = -40 ∧
      activityTotal act4 CashActivity.financing cash4 = 30 ∧
      endingCash 20 cash4 = 110 := by
  have hfil_op : Finset.univ.filter (fun i : Fin 4 => act4 i = CashActivity.operating) = {0} := by
    decide
  have hfil_inv : Finset.univ.filter (fun i : Fin 4 => act4 i = CashActivity.investing) = {1} := by
    decide
  have hfil_fin : Finset.univ.filter (fun i : Fin 4 => act4 i = CashActivity.financing) = {2} := by
    decide
  have c0 : cash4 0 = 100 := rfl
  have c1 : cash4 1 = -40 := rfl
  have c2 : cash4 2 = 30 := rfl
  have c3 : cash4 3 = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold activityTotal
    rw [hfil_op, Finset.sum_singleton, c0]
  · unfold activityTotal
    rw [hfil_inv, Finset.sum_singleton, c1]
  · unfold activityTotal
    rw [hfil_fin, Finset.sum_singleton, c2]
  · unfold endingCash
    rw [Fin.sum_univ_four, c0, c1, c2, c3]
    norm_num

/-- A noncash-labelled transaction carrying cash breaks the reconciliation. -/
theorem test_noncash_with_cash_breaks :
    activityTotal act4 CashActivity.operating ![100, -40, 30, -10] +
        activityTotal act4 CashActivity.investing ![100, -40, 30, -10] +
        activityTotal act4 CashActivity.financing ![100, -40, 30, -10] ≠
      endingCash 20 ![100, -40, 30, -10] - 20 := by
  have hfil_op : Finset.univ.filter (fun i : Fin 4 => act4 i = CashActivity.operating) = {0} := by
    decide
  have hfil_inv : Finset.univ.filter (fun i : Fin 4 => act4 i = CashActivity.investing) = {1} := by
    decide
  have hfil_fin : Finset.univ.filter (fun i : Fin 4 => act4 i = CashActivity.financing) = {2} := by
    decide
  have c0 : ((![100, -40, 30, -10] : Fin 4 → ℝ) 0) = 100 := rfl
  have c1 : ((![100, -40, 30, -10] : Fin 4 → ℝ) 1) = -40 := rfl
  have c2 : ((![100, -40, 30, -10] : Fin 4 → ℝ) 2) = 30 := rfl
  have c3 : ((![100, -40, 30, -10] : Fin 4 → ℝ) 3) = -10 := rfl
  unfold activityTotal endingCash
  rw [hfil_op, hfil_inv, hfil_fin]
  simp only [Finset.sum_singleton]
  rw [Fin.sum_univ_four, c0, c1, c2, c3]
  norm_num

/-- The four-transaction example reconciles to the change in cash, by `operating_add_investing_add_financing`. -/
theorem test_cashFlow4_reconciles :
    activityTotal act4 CashActivity.operating cash4 + activityTotal act4 CashActivity.investing cash4 +
        activityTotal act4 CashActivity.financing cash4 =
      endingCash 20 cash4 - 20 := by
  exact operating_add_investing_add_financing act4 cash4 20 (fun i hi => by
    fin_cases i
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
    · rfl)

/-- For the four-transaction classification, any cash effects with zero noncash cash reconcile. -/
theorem test_any_cash_reconciles (cash : Fin 4 → ℝ) (h3 : cash 3 = 0) :
    activityTotal act4 CashActivity.operating cash + activityTotal act4 CashActivity.investing cash +
        activityTotal act4 CashActivity.financing cash =
      endingCash 20 cash - 20 := by
  exact operating_add_investing_add_financing act4 cash 20 (fun i hi => by
    fin_cases i
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
    · exact absurd hi (by decide)
    · exact h3)

/-- An empty period: ending cash equals opening cash and every activity total is zero. -/
theorem test_empty_period (opening : ℝ) :
    endingCash opening (Fin.elim0 : Fin 0 → ℝ) = opening ∧
      activityTotal (Fin.elim0 : Fin 0 → CashActivity) CashActivity.operating
          (Fin.elim0 : Fin 0 → ℝ) +
        activityTotal (Fin.elim0 : Fin 0 → CashActivity) CashActivity.investing
          (Fin.elim0 : Fin 0 → ℝ) +
        activityTotal (Fin.elim0 : Fin 0 → CashActivity) CashActivity.financing
          (Fin.elim0 : Fin 0 → ℝ) = 0 := by
  have h_main := operating_add_investing_add_financing (Fin.elim0 : Fin 0 → CashActivity)
    (Fin.elim0 : Fin 0 → ℝ) opening (fun i _ => Fin.elim0 i)
  have h_end : endingCash opening (Fin.elim0 : Fin 0 → ℝ) = opening := by
    simp [endingCash]
  refine ⟨h_end, ?_⟩
  rw [h_main, h_end, sub_self]

end MathlibExtTest.Economics.Accounting.CashFlowStatement
