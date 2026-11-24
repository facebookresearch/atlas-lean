# On a mission ledger, the stored energy changes by the battery flow

Let `s₀` be initial stocks and `flow` signed flows of a mission ledger indexed by resources, and let
resource `e` have the [battery flow](battery-flow.md) as its flow. Then for every interval `k`, its
[stock](../../classical-mechanics/flight-and-spaceflight/mission-resource-ledgers-and-burn-costs/stock.md)
satisfies

`stock_e(k + 1) = stock_e(k) + dt_k (η_c P_{c,k} - P_{d,k} / η_d)`.
