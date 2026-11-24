# Principal portion of a loan payment

The principal repaid in period `t + 1` (`t = 0, 1, 2, …`) is the payment minus the interest
accrued on the opening balance, `P_{t+1} - r B_t`, where `B_t` is the outstanding balance of
the loan: `B_0 = L` and `B_{t+1} = (1 + r) B_t - P_{t+1}`.
