---
article_id: af_6af781246d33fe84adb1e2b3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing.one_period_fundamental_theorem_asset_pricing
---

# One period fundamental theorem asset pricing

Finite one-period FTAP: no arbitrage iff strictly positive state-price / martingale pmf with zero
expected gain exists.

## Depends on

This node has no prerequisites.

## Proof depends on

- [One period fundamental theorem asset pricing general](one-period-fundamental-theorem-asset-pri.md)

## Sources

- [MathlibExt, MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing](../../../../../../sources/v2/MathlibExt.md)
- J. M. Harrison and D. M. Kreps, J. Econom. Theory 20 (1979), DOI 10.1016/0022-0531(79)90043-7. Proves `Wanted` entry `one_period_fundamental_theorem_asset_pricing`. It follows from `one_period_fundamental_theorem_asset_pricing_general`; the unused `[DecidableEq Ω]` and `[DecidableEq A]` keep the source's shape.
