# Truncated discounted value as a present value

For any real `β`, rewards `r_t` and horizon `T`, the `T`-period truncation
`∑_{t=0}^{T-1} βᵗ r_t` of the discounted value is the present value of the first `T` rewards
`r_0, …, r_{T-1}`, paid at the dates `0, …, T - 1`, under the discount factors `D_t = βᵗ`.
