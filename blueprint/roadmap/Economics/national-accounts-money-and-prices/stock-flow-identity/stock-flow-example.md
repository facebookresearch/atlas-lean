# Stock Flow example

The concrete stock satisfies the stock-flow identity at `n = 2`: `K 2 = 118`.
Prove by applying `stock_eq_initial_add_flows` with constant inflow `10`, outflow `3`,
other change `2`, discharging the per-period accounting by `simp [exampleStock]` and `ring`,
then evaluating the finite sums.
