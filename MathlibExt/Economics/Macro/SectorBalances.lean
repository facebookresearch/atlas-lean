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
(gross, domestic, expenditure approach), split without overlap into personal consumption
expenditure `C`, gross private domestic investment `I`, government consumption expenditure and
gross investment `G` (purchases of final goods and services, not transfers), and net exports
`NX = X - M`; `T` is taxes net of transfers; accounting is not a causal model. The accounting
laws are fields of `SectorAccounts`, so only consistent accounts inhabit the type. Substituting
the net-export law into the GDP law gives the expenditure identity; combining income disposal,
public saving, national saving, the GDP law, and the net-export law gives the
saving-investment balance: national saving finances private investment plus net exports.

Open-economy simplification: income disposal `Y = C + Sp + T` treats GDP as national
disposable income, so these accounts assume zero net primary income and zero net current
transfers from the rest of the world. Under that assumption the current-account balance equals
net exports. Without it, national saving equals investment plus the current-account balance,
not investment plus net exports.

## Main results

* `expenditure_identity`: `Y = C + I + G + NX`.
* `saving_investment_balance`: `S = I + NX`, under the simplification above.
* `sectorAccounts_example`: the concrete accounts `Y = 110, S = 25` satisfy both.

## References

* MIT 14.05 Intermediate Macroeconomics, Fall 2024, syllabus (measurement scope).
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.SectorBalances

/-- Sector accounts for one period, in nominal terms, under the conventions pinned below. The
accounting laws are fields, so a record cannot violate them.

* `Y` is GDP (gross domestic product, expenditure approach): the value of final goods and
  services produced domestically in the period. Gross means no depreciation is subtracted;
  domestic means production inside the borders, not the product of nationals.
* The expenditure components do not overlap: `C` is personal (household) consumption
  expenditure, `I` is gross private domestic investment, `G` is government consumption
  expenditure and gross investment (government purchases of final goods and services, not
  transfers), `X` is exports and `M` is imports of goods and services.
* `Sp` is private saving and `T` is taxes net of transfers. `Sg = T - G` is public saving in
  the textbook sense: since `G` includes government gross investment, public investment is
  not counted as saving, matching `I`, which counts only private investment. `S = Sp + Sg` is
  national saving in the same sense (`Y - C - G`), and `NX` is net exports.
* Open-economy simplification: income disposal treats GDP as national disposable income, so
  net primary income and net current transfers from the rest of the world are assumed zero,
  and the current-account balance equals `NX`.
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
  /-- GDP by expenditure: `Y = C + I + G + (X - M)`. -/
  gdp : Y = C + I + G + (X - M)
  /-- Net exports: `NX = X - M`. -/
  netExports : NX = X - M
  /-- Income disposal: `Y = C + Sp + T`. This treats GDP as national disposable income, i.e.
  zero net primary income and zero net current transfers from the rest of the world. -/
  incomeDisposal : Y = C + Sp + T
  /-- Public saving: `Sg = T - G`. -/
  publicSaving : Sg = T - G
  /-- National saving: `S = Sp + Sg`. -/
  nationalSaving : S = Sp + Sg

/-- **Expenditure identity.** Substituting the net-export law `NX = X - M` into the GDP
expenditure law `Y = C + I + G + (X - M)` gives `Y = C + I + G + NX`. -/
theorem expenditure_identity (a : SectorAccounts) : a.Y = a.C + a.I + a.G + a.NX := by
  linarith [a.gdp, a.netExports]

/-- **Saving-investment balance.** Income disposal (`Y = C + Sp + T`), public saving
(`Sg = T - G`), national saving (`S = Sp + Sg`), the GDP expenditure law, and the net-export
law together give `S = I + NX`: national saving finances private investment plus net exports
(equivalently `S - I = NX`). This relies on the open-economy simplification pinned in
`SectorAccounts` (zero net primary income and net current transfers from abroad); in general
the right side is investment plus the current-account balance. -/
theorem saving_investment_balance (a : SectorAccounts) : a.S = a.I + a.NX := by
  linarith [a.gdp, a.netExports, a.incomeDisposal, a.publicSaving, a.nationalSaving]

/-- Concrete sector accounts: `C = 70`, `I = 20`, `G = 15`, `X = 25`, `M = 20`, so
`Y = 110` and `NX = 5`; with taxes net of transfers `T = 20`, private saving `Sp = 20`,
public saving `Sg = 5`, national saving `S = 25 = I + NX`. -/
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
  gdp := by norm_num
  netExports := by norm_num
  incomeDisposal := by norm_num
  publicSaving := by norm_num
  nationalSaving := by norm_num

/-- The concrete accounts satisfy both the expenditure identity and the saving-investment
balance: both identities hold at `exampleAccounts`. -/
theorem sectorAccounts_example :
    exampleAccounts.Y = exampleAccounts.C + exampleAccounts.I + exampleAccounts.G +
        exampleAccounts.NX ∧
      exampleAccounts.S = exampleAccounts.I + exampleAccounts.NX :=
  ⟨expenditure_identity _, saving_investment_balance _⟩

end MathlibExt.Economics.Macro.SectorBalances
