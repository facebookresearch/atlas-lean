/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The cash conversion cycle

Working-capital data for one period and the cash conversion cycle (cash cycle) computed from it,
following OpenStax, *Principles of Finance*, §19.1, equations 19.4–19.13.

## i. Overview

Turnover ratios divide a flow over the period by an average balance: inventory turnover is cost of
goods sold over average inventory, accounts receivable turnover is credit sales over average
receivables, and accounts payable turnover is cost of goods sold over average payables. Each
period in days is `periodDays / turnover`. The cash conversion cycle is the inventory conversion
period plus the receivables collection period minus the payables deferral period. It is negative
when suppliers are paid later than cash is collected.

This file is a specification: it records the definition and states no theorem about it. Lean's
`x / 0 = 0` makes a period `0` when its turnover or balance is zero; such values are not
meaningful. Whether balances are averages (the source's convention) or ending balances is
recorded in the data, not in the formula.

## ii. Main definitions

* `MathlibExt.Economics.Accounting.WorkingCapitalData`: balances, flows and period length.
* `MathlibExt.Economics.Accounting.WorkingCapitalData.cashConversionCycle`: the cash conversion cycle, with
  its components `inventoryConversionPeriod`, `receivablesCollectionPeriod` and
  `payablesDeferralPeriod`.

## iii. References

* OpenStax, *Principles of Finance*, §19.1 "What Is Working Capital?",
  https://openstax.org/books/principles-finance/pages/19-1-what-is-working-capital
-/

@[expose] public section

namespace MathlibExt.Economics.Accounting

/-- Working-capital data for one period. Balances are currency amounts; `creditSales` and
`costOfGoodsSold` are currency amounts over the period; `periodDays` is the length of the period
in days (`365` in the source). -/
structure WorkingCapitalData where
  /-- Average accounts receivable over the period (source eq. 19.9). -/
  receivables : ℝ
  /-- Average inventory over the period (source eq. 19.6). -/
  inventory : ℝ
  /-- Average accounts payable over the period (source eq. 19.12). -/
  payables : ℝ
  /-- Credit sales over the period. -/
  creditSales : ℝ
  /-- Cost of goods sold over the period. -/
  costOfGoodsSold : ℝ
  /-- Length of the period in days. -/
  periodDays : ℝ

namespace WorkingCapitalData

/-- Inventory turnover ratio `cost of goods sold / average inventory` (source eq. 19.5). -/
noncomputable def inventoryTurnover (d : WorkingCapitalData) : ℝ :=
  d.costOfGoodsSold / d.inventory

/-- Accounts receivable turnover `credit sales / average accounts receivable`
(source eq. 19.8). -/
noncomputable def receivablesTurnover (d : WorkingCapitalData) : ℝ :=
  d.creditSales / d.receivables

/-- Accounts payable turnover `cost of goods sold / average accounts payable`
(source eq. 19.11). -/
noncomputable def payablesTurnover (d : WorkingCapitalData) : ℝ :=
  d.costOfGoodsSold / d.payables

/-- Inventory conversion period (days of inventory, DIO) `periodDays / inventory turnover`
(source eq. 19.7). Meaningful only for nonzero turnover (Lean's `x / 0 = 0` otherwise). -/
noncomputable def inventoryConversionPeriod (d : WorkingCapitalData) : ℝ :=
  d.periodDays / d.inventoryTurnover

/-- Receivables collection period (days sales outstanding, DSO)
`periodDays / accounts receivable turnover` (source eq. 19.10). -/
noncomputable def receivablesCollectionPeriod (d : WorkingCapitalData) : ℝ :=
  d.periodDays / d.receivablesTurnover

/-- Payables deferral period (days in payables, DPO) `periodDays / accounts payable turnover`
(source eq. 19.13). -/
noncomputable def payablesDeferralPeriod (d : WorkingCapitalData) : ℝ :=
  d.periodDays / d.payablesTurnover

/-- The cash conversion cycle, in days: inventory conversion period plus receivables collection
period minus payables deferral period (source eq. 19.4). It is negative when suppliers are paid
later than cash is collected. -/
noncomputable def cashConversionCycle (d : WorkingCapitalData) : ℝ :=
  d.inventoryConversionPeriod + d.receivablesCollectionPeriod - d.payablesDeferralPeriod

end WorkingCapitalData

end MathlibExt.Economics.Accounting
