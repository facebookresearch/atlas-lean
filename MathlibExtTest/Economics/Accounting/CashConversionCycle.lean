/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Accounting.CashConversionCycle

import Mathlib.Tactic.NormNum

/-!
# Tests for the cash conversion cycle

The source's worked example (King Sized Products, OpenStax *Principles of Finance* §19.1) with
exact values (the source rounds the cycle to `57.2` days), a supplier-financed firm with a negative
cycle, and the zero-balance edge case of Lean's division convention.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Accounting.CashConversionCycle

open _root_.Economics.Accounting

/-- The source's worked example (King Sized Products, OpenStax §19.1, Think It Through):
credit sales 40,000,000, average inventory 3,000,000, average receivables 6,000,000, average
payables 2,800,000, cost of goods sold 30,000,000, a 365-day year. -/
noncomputable def kingSizedProducts : WorkingCapitalData :=
  { receivables := 6000000, inventory := 3000000, payables := 2800000,
    creditSales := 40000000, costOfGoodsSold := 30000000, periodDays := 365 }

theorem kingSizedProducts_inventoryConversionPeriod :
    kingSizedProducts.inventoryConversionPeriod = 73 / 2 := by
  simp only [kingSizedProducts, WorkingCapitalData.inventoryConversionPeriod,
    WorkingCapitalData.inventoryTurnover]
  norm_num

theorem kingSizedProducts_receivablesCollectionPeriod :
    kingSizedProducts.receivablesCollectionPeriod = 219 / 4 := by
  simp only [kingSizedProducts, WorkingCapitalData.receivablesCollectionPeriod,
    WorkingCapitalData.receivablesTurnover]
  norm_num

theorem kingSizedProducts_payablesDeferralPeriod :
    kingSizedProducts.payablesDeferralPeriod = 511 / 15 := by
  simp only [kingSizedProducts, WorkingCapitalData.payablesDeferralPeriod,
    WorkingCapitalData.payablesTurnover]
  norm_num

/-- Exact value of the source's rounded `57.2` days. -/
theorem kingSizedProducts_cashConversionCycle :
    kingSizedProducts.cashConversionCycle = 3431 / 60 := by
  simp only [kingSizedProducts, WorkingCapitalData.cashConversionCycle,
    WorkingCapitalData.inventoryConversionPeriod, WorkingCapitalData.inventoryTurnover,
    WorkingCapitalData.receivablesCollectionPeriod, WorkingCapitalData.receivablesTurnover,
    WorkingCapitalData.payablesDeferralPeriod, WorkingCapitalData.payablesTurnover]
  norm_num

/-- A supplier-financed firm: receivables 10, inventory 30, payables 150, credit sales 1200,
cost of goods sold 900, a 360-day year. -/
noncomputable def supplierFinancedFirm : WorkingCapitalData :=
  { receivables := 10, inventory := 30, payables := 150, creditSales := 1200,
    costOfGoodsSold := 900, periodDays := 360 }

theorem supplierFinancedFirm_cashConversionCycle :
    supplierFinancedFirm.cashConversionCycle = -45 := by
  simp only [supplierFinancedFirm, WorkingCapitalData.cashConversionCycle,
    WorkingCapitalData.inventoryConversionPeriod, WorkingCapitalData.inventoryTurnover,
    WorkingCapitalData.receivablesCollectionPeriod, WorkingCapitalData.receivablesTurnover,
    WorkingCapitalData.payablesDeferralPeriod, WorkingCapitalData.payablesTurnover]
  norm_num

/-- Zero-inventory edge: with `inventory := 0`, the inventory conversion period is `0` by Lean's
division convention (`x / 0 = 0`); this value is meaningless as a days-of-inventory measure. -/
example : ({ kingSizedProducts with inventory := 0 }.inventoryConversionPeriod) = 0 := by
  simp only [WorkingCapitalData.inventoryConversionPeriod,
    WorkingCapitalData.inventoryTurnover, kingSizedProducts]
  norm_num

end MathlibExtTest.Economics.Accounting.CashConversionCycle
