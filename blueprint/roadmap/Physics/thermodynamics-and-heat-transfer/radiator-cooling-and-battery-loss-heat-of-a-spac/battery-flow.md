# Stored-energy flow of a battery on one schedule interval

For efficiencies `η_c`, `η_d` and, on each schedule interval `k`, a duration `dt_k`, a charge power
`P_{c,k}` and a discharge power `P_{d,k}`, the battery flow of interval `k` is
`dt_k (η_c P_{c,k} - P_{d,k} / η_d)`, the stored-energy flow of the interval: for a mission ledger
whose resource has this flow, the stock changes by this amount over interval `k`
([stock update](stock-battery-flow-succ.md)). With the convention `u / 0 = 0`, `P_{d,k} / η_d = 0`
when `η_d = 0`.
