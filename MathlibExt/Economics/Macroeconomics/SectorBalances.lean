/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Sector accounts, the expenditure identity, and the saving-investment balance

Sector accounts for one period in nominal terms, under pinned conventions: `Y` is GDP
(gross, domestic, expenditure approach), `G` is government purchases of final goods and
services (not transfers), `T` is taxes net of transfers, and accounting is not a causal
model. Substituting the net-export definition into the GDP definition gives the
expenditure identity; combining income disposal, government saving, national saving, the
expenditure identity, and the net-export definition gives the saving-investment balance:
national saving finances domestic investment plus net exports.

## Main results

* `expenditure_identity`: `Y = C + I + G + NX` from the GDP definition and `NX = X - M`.
* `saving_investment_balance`: `S = I + NX`.
* `sectorAccounts_example`: the concrete accounts `Y = 110, S = 25` satisfy both.

## References

* MIT 14.05 Intermediate Macroeconomics, Fall 2024, syllabus (measurement scope).
-/

@[expose] public section

namespace MathlibExt.Economics.Macroeconomics.SectorBalances

/-- Sector accounts for one period, in nominal terms, under the conventions pinned below.

* `Y` is GDP (gross domestic product, expenditure approach): the value of final goods and
  services produced domestically in the period. Gross means no depreciation is subtracted;
  domestic means production inside the borders, not the product of nationals.
* `C` is final consumption expenditure, `I` is gross investment, `G` is government purchases
  of final goods and services (not transfers), `X` is exports, `M` is imports.
* `Sp` is private saving, `T` is taxes net of transfers, `Sg` is government saving,
  `S` is national saving, `NX` is net exports.
* Accounting only, not a causal model: no behavioural relation between the fields is assumed.
  Transfers are inside `T`, not inside `G` or `Y`; intermediate goods are not counted in `Y`.
-/
structure SectorAccounts where
  Y : ℝ
  C : ℝ
  I : ℝ
  G : ℝ
  X : ℝ
  M : ℝ
  Sp : ℝ
  T : ℝ
  Sg : ℝ
  S : ℝ
  NX : ℝ

/-- **Expenditure identity.** Substituting the net-export definition `NX = X - M` into the
GDP expenditure definition `Y = C + I + G + (X - M)` gives `Y = C + I + G + NX`. -/
theorem expenditure_identity (a : SectorAccounts)
    (hY : a.Y = a.C + a.I + a.G + (a.X - a.M)) (hNX : a.NX = a.X - a.M) :
    a.Y = a.C + a.I + a.G + a.NX := by
  linarith

/-- **Saving-investment balance.** Income disposal (`Y = C + Sp + T`), government saving
(`Sg = T - G`), national saving (`S = Sp + Sg`), the expenditure identity, and the net-export
definition together give `S = I + NX`: national saving finances domestic investment plus net
exports (equivalently `S - I = NX`). -/
theorem saving_investment_balance (a : SectorAccounts)
    (hY : a.Y = a.C + a.I + a.G + (a.X - a.M))
    (hIncome : a.Y = a.C + a.Sp + a.T) (hSg : a.Sg = a.T - a.G)
    (hS : a.S = a.Sp + a.Sg) (hNX : a.NX = a.X - a.M) :
    a.S = a.I + a.NX := by
  linarith

/-- Concrete sector accounts: `C = 70`, `I = 20`, `G = 15`, `X = 25`, `M = 20`, so
`Y = 110` and `NX = 5`; with taxes net of transfers `T = 20`, private saving `Sp = 20`,
government saving `Sg = 5`, national saving `S = 25 = I + NX`. -/
def exampleAccounts : SectorAccounts where
  Y := 110
  C := 70
  I := 20
  G := 15
  X := 25
  M := 20
  Sp := 20
  T := 20
  Sg := 5
  S := 25
  NX := 5

/-- The concrete accounts satisfy both the expenditure identity and the saving-investment
balance: both identities hold at `exampleAccounts`. -/
theorem sectorAccounts_example :
    exampleAccounts.Y = exampleAccounts.C + exampleAccounts.I + exampleAccounts.G +
        exampleAccounts.NX ∧
      exampleAccounts.S = exampleAccounts.I + exampleAccounts.NX := by
  constructor
  · exact expenditure_identity _ (by norm_num [exampleAccounts]) (by norm_num [exampleAccounts])
  · exact saving_investment_balance _ (by norm_num [exampleAccounts])
      (by norm_num [exampleAccounts]) (by norm_num [exampleAccounts])
      (by norm_num [exampleAccounts]) (by norm_num [exampleAccounts])

end MathlibExt.Economics.Macroeconomics.SectorBalances
