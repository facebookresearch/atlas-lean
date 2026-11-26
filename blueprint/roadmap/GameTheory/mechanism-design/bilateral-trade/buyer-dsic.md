# Buyer DSIC

Dominant-strategy incentive compatibility for the buyer, for types and
reports in `[0, 1]`: against every seller report, truthful reporting maximizes buyer utility.
For each seller report `s` this is `SingleParameter.IsIncentiveCompatibleOn` on `[0, 1]` with
allocation `M.alloc s` and payment `fun r => M.alloc s r * M.payBuyer s r`. It is stated per
side, not bundled with `SellerDSIC` as in `IsDominantStrategyIncentiveCompatible`, because each
threshold price uses one side's condition.
