# Sector Accounts

An assumption bundle of sector accounts for one period, in nominal terms, following
SNA 2008 under the simplifications pinned below. The law fields are hypotheses: a record is a
choice of aggregates together with evidence that they satisfy the accounting identities, which
are assumed here, not derived from transaction-level data.

* `Y` is GDP (gross domestic product, expenditure approach): final consumption expenditure plus
  gross capital formation plus exports less imports (SNA 2008, §16.47). Gross means no
  depreciation is subtracted; domestic means production inside the borders, not the product of
  nationals.
* The expenditure components are read as nonoverlapping (a convention):
  `C` is private final consumption expenditure (households and non-profit institutions serving
  households), `G` is government final consumption expenditure (consumption only, no
  investment), `I` is gross capital formation of all resident sectors, private and government
  (so government investment is in `I`), `X` is exports and `M` is imports of goods and services.
* `T` is net taxes: taxes and other current receipts of government less the current transfers
  and property income it pays to the private sector. It is government disposable income, and
  `Y - T` is private disposable income.
* Saving is disposable income less final consumption expenditure, after the pension-entitlement
  adjustment pinned below (SNA 2008, §9.26), gross of consumption of fixed capital like `I`:
  `Sp` is private saving, `Sg = T - G` is government saving, and `S = Sp + Sg` is national
  saving (`Y - C - G`). Government investment is not consumption, so it is not subtracted from
  `Sg`. `NX` is net exports.
* Open-economy simplification: income disposal treats GDP as national disposable income, so
  net primary income and net current transfers from the rest of the world are assumed zero,
  and the current-account balance equals `NX` (SNA 2008's current external balance, recorded
  from the rest of the world's side, is `-NX`).
* Pension-entitlement simplification: SNA 2008 derives saving after the adjustment for the
  change in pension entitlements (D.8; §9.26), which the units paying the pensions record with
  the opposite sign (§9.25). The accounts assume zero net pension-entitlement adjustment between
  the private and government sectors, so `Sp` and `Sg` carry no D.8 term; such an adjustment
  would move saving between them without changing `S`.
* Accounting only, not a causal model: no behavioural relation between the fields is assumed.
  Transfers are inside `T`, not inside `G` or `Y`; intermediate goods are not counted in `Y`.
