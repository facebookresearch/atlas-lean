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
five national-accounts identities they are assumed to satisfy (GDP by expenditure, net exports,
private saving, government saving, national saving). The identities are hypotheses supplied when
a record is built; nothing here derives them from a classification of transactions.

The aggregates follow the System of National Accounts 2008 (SNA 2008). GDP by expenditure is
final consumption expenditure plus gross capital formation plus exports less imports
(SNA 2008, §16.47). Final consumption is split between the private sector, `C`, and general
government, `G`, so `G` is government final consumption expenditure only. Gross capital
formation `I` covers all resident sectors, so government investment is part of `I`, not of `G`.
Saving is disposable income less final consumption expenditure (SNA 2008, §9.26). With `T` the
government's disposable income (taxes net of transfers), private saving is `Sp = (Y - T) - C`,
government saving is `Sg = T - G`, and national saving is `S = Sp + Sg = Y - C - G`. Government
investment is not consumption, so it is not subtracted from saving; it is part of the
investment that saving finances.

`saving_investment_balance` derives `S = I + NX` by combining all five identities: national
saving equals gross capital formation, private and government, plus net exports.

Open-economy simplification: income disposal `Y = C + Sp + T` treats GDP as national
disposable income, so these accounts assume zero net primary income and zero net current
transfers from the rest of the world. Under that assumption the economy's current-account
balance equals net exports. Without it, national saving equals gross capital formation plus the
current-account balance, which adds net primary income and net current transfers from abroad to
net exports. SNA 2008 records this balance from the rest of the world's side, as the current
external balance (§16.42), which has the opposite sign: under the simplification it is
`M - X = -NX`, and the identity reads `S = I -` (current external balance).

## Main results

* `saving_investment_balance`: `S = I + NX`, derived from the five assumed identities under the
  simplification above.
* `sectorAccounts_example`: the concrete accounts with `Y = 110` and `S = 25` satisfy the GDP
  identity (assumed) and the saving-investment balance (derived).

## References

* European Commission, IMF, OECD, United Nations and World Bank,
  *System of National Accounts 2008* (2009): Chapter 9 (The use of income accounts), §9.26,
  saving as disposable income less final consumption expenditure; Chapter 16 (Summarizing and
  integrating the accounts), §16.42–16.43, the consolidated current accounts and the current
  external balance of the rest of the world, and §16.47, the expenditure measure of GDP.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.SectorBalances

/-- An assumption bundle of sector accounts for one period, in nominal terms, following
SNA 2008 under the simplifications pinned below. The law fields are hypotheses: a record is a
choice of aggregates together with evidence that they satisfy the accounting identities, which
are assumed here, not derived from transaction-level data.

* `Y` is GDP (gross domestic product, expenditure approach): final consumption expenditure plus
  gross capital formation plus exports less imports (SNA 2008, §16.47). Gross means no
  depreciation is subtracted; domestic means production inside the borders, not the product of
  nationals.
* The expenditure components are read as nonoverlapping (a convention, not checked by Lean):
  `C` is private final consumption expenditure (households and non-profit institutions serving
  households), `G` is government final consumption expenditure (consumption only, no
  investment), `I` is gross capital formation of all resident sectors, private and government
  (so government investment is in `I`), `X` is exports and `M` is imports of goods and services.
* `T` is net taxes: taxes and other current receipts of government less the current transfers
  and property income it pays to the private sector. It is government disposable income, and
  `Y - T` is private disposable income.
* Saving is disposable income less final consumption expenditure (SNA 2008, §9.26), gross of
  consumption of fixed capital like `I`: `Sp` is private saving, `Sg = T - G` is government
  saving, and `S = Sp + Sg` is national saving (`Y - C - G`). Government investment is not
  consumption, so it is not subtracted from `Sg`. `NX` is net exports.
* Open-economy simplification: income disposal treats GDP as national disposable income, so
  net primary income and net current transfers from the rest of the world are assumed zero,
  and the current-account balance equals `NX` (SNA 2008's current external balance, recorded
  from the rest of the world's side, is `-NX`).
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
  /-- Assumed identity, GDP by expenditure: `Y = C + I + G + (X - M)`, final consumption
  `C + G` plus gross capital formation `I` plus exports less imports. -/
  gdp : Y = C + I + G + (X - M)
  /-- Assumed identity, net exports: `NX = X - M`. -/
  netExports : NX = X - M
  /-- Assumed identity, private income disposal: `Y = C + Sp + T`, so private saving is private
  disposable income `Y - T` less private final consumption `C`. This treats GDP as national
  disposable income, i.e. zero net primary income and zero net current transfers from the rest
  of the world. -/
  incomeDisposal : Y = C + Sp + T
  /-- Assumed identity, government saving: `Sg = T - G`, government disposable income less
  government final consumption. -/
  publicSaving : Sg = T - G
  /-- Assumed identity, national saving: `S = Sp + Sg`. -/
  nationalSaving : S = Sp + Sg

/-- **Saving-investment balance.** The five assumed identities of `SectorAccounts`, GDP by
expenditure, net exports, private income disposal (`Y = C + Sp + T`), government saving
(`Sg = T - G`), and national saving (`S = Sp + Sg`), together give `S = I + NX`: national
saving finances gross capital formation, private and government, plus net exports
(equivalently `S - I = NX`). This relies on the open-economy simplification pinned in
`SectorAccounts` (zero net primary income and net current transfers from abroad); in general
the right side is gross capital formation plus the current-account balance (the negative of
SNA 2008's current external balance). -/
theorem saving_investment_balance (a : SectorAccounts) : a.S = a.I + a.NX := by
  linarith [a.gdp, a.netExports, a.incomeDisposal, a.publicSaving, a.nationalSaving]

/-- Concrete sector accounts: private consumption `C = 70`, gross capital formation `I = 20`
(private and government), government consumption `G = 15`, `X = 25`, `M = 20`, so `Y = 110`
and `NX = 5`; with net taxes `T = 20`, private saving `Sp = 20`, government saving `Sg = 5`,
national saving `S = 25 = I + NX`. -/
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

/-- The concrete accounts satisfy the identities checked by `norm_num` when `exampleAccounts`
is built. The first conjunct is the assumed GDP identity in net-export form (the record laws
`gdp` and `netExports`); the second is the derived saving-investment balance. -/
theorem sectorAccounts_example :
    exampleAccounts.Y = exampleAccounts.C + exampleAccounts.I + exampleAccounts.G +
        exampleAccounts.NX ∧
      exampleAccounts.S = exampleAccounts.I + exampleAccounts.NX :=
  ⟨by linarith [exampleAccounts.gdp, exampleAccounts.netExports], saving_investment_balance _⟩

end MathlibExt.Economics.Macro.SectorBalances
