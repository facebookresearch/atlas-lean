# Principal repayments sum to the loan once it is paid off

Let `B_t` be the outstanding balance of a loan `L` at rate `r` with payments `P_t`
(`B_0 = L`, `B_{t+1} = (1 + r) B_t - P_{t+1}`). If the balance after `n` periods is zero,
`B_n = 0`, the principal repayments over those periods sum to the initial loan:
`∑_{t=0}^{n-1} (P_{t+1} - r B_t) = L`.
