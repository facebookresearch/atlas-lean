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
# Sector-account identities and the saving-investment balance

`SectorAccounts` is an assumption bundle: eleven nominal aggregates for one period together with
the national-accounts identities they are assumed to satisfy (GDP by expenditure, net exports,
income disposal, public saving, national saving). The identities are hypotheses supplied when a
record is built; nothing here derives them from a classification of transactions. The pinned
conventions are: `Y` is GDP (gross, domestic, expenditure approach), read as split without
overlap into personal consumption expenditure `C`, gross private domestic investment `I`,
government consumption expenditure and gross investment `G` (purchases of final goods and
services, not transfers), and net exports `NX = X - M`; `T` is taxes net of transfers;
accounting is not a causal model. The nonoverlapping reading of `C`, `I`, `G` is a documented
convention that Lean does not check.

From the bundle, `expenditure_identity` restates the assumed GDP identity with the assumed
net-export identity substituted (no further accounting content), and
`saving_investment_balance` derives `S = I + NX` by combining all five identities: national
saving finances private investment plus net exports.

Open-economy simplification: income disposal `Y = C + Sp + T` treats GDP as national
disposable income, so these accounts assume zero net primary income and zero net current
transfers from the rest of the world. Under that assumption the current-account balance equals
net exports. Without it, national saving equals investment plus the current-account balance,
not investment plus net exports.

## Main results

* `expenditure_identity`: `Y = C + I + G + NX`, the assumed GDP identity rewritten with `NX`.
* `saving_investment_balance`: `S = I + NX`, derived from the five assumed identities under the
  simplification above.
* `sectorAccounts_example`: the concrete accounts `Y = 110, S = 25` satisfy both.

## References

* MIT 14.05 Intermediate Macroeconomics, Fall 2024, syllabus (measurement scope).
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.SectorBalances

/-- An assumption bundle of sector accounts for one period, in nominal terms, under the
conventions pinned below. The law fields are hypotheses: a record is a choice of aggregates
together with evidence that they satisfy the accounting identities, which are assumed here, not
derived from transaction-level data.

* `Y` is GDP (gross domestic product, expenditure approach): the value of final goods and
  services produced domestically in the period. Gross means no depreciation is subtracted;
  domestic means production inside the borders, not the product of nationals.
* The expenditure components are read as nonoverlapping (a convention, not checked by Lean):
  `C` is personal (household) consumption expenditure, `I` is gross private domestic
  investment, `G` is government consumption expenditure and gross investment (government
  purchases of final goods and services, not transfers), `X` is exports and `M` is imports of
  goods and services.
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
  /-- Assumed identity, GDP by expenditure: `Y = C + I + G + (X - M)`. -/
  gdp : Y = C + I + G + (X - M)
  /-- Assumed identity, net exports: `NX = X - M`. -/
  netExports : NX = X - M
  /-- Assumed identity, income disposal: `Y = C + Sp + T`. This treats GDP as national
  disposable income, i.e. zero net primary income and zero net current transfers from the rest
  of the world. -/
  incomeDisposal : Y = C + Sp + T
  /-- Assumed identity, public saving: `Sg = T - G`. -/
  publicSaving : Sg = T - G
  /-- Assumed identity, national saving: `S = Sp + Sg`. -/
  nationalSaving : S = Sp + Sg

/-- **Expenditure identity.** The assumed GDP identity `Y = C + I + G + (X - M)` with the
assumed net-export identity `NX = X - M` substituted. This restates assumptions of
`SectorAccounts`; it is not derived from a classification of final expenditures. -/
theorem expenditure_identity (a : SectorAccounts) : a.Y = a.C + a.I + a.G + a.NX := by
  linarith [a.gdp, a.netExports]

/-- **Saving-investment balance.** The five assumed identities of `SectorAccounts`, income
disposal (`Y = C + Sp + T`), public saving (`Sg = T - G`), national saving (`S = Sp + Sg`), GDP
by expenditure, and net exports, together give `S = I + NX`: national saving finances private
investment plus net exports (equivalently `S - I = NX`). This relies on the open-economy
simplification pinned in `SectorAccounts` (zero net primary income and net current transfers
from abroad); in general the right side is investment plus the current-account balance. -/
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

/-- The concrete accounts satisfy the assumed identities (checked by `norm_num` when
`exampleAccounts` is built), so the expenditure identity and the saving-investment balance hold
at `exampleAccounts`. -/
theorem sectorAccounts_example :
    exampleAccounts.Y = exampleAccounts.C + exampleAccounts.I + exampleAccounts.G +
        exampleAccounts.NX ∧
      exampleAccounts.S = exampleAccounts.I + exampleAccounts.NX :=
  ⟨expenditure_identity _, saving_investment_balance _⟩

end MathlibExt.Economics.Macro.SectorBalances
