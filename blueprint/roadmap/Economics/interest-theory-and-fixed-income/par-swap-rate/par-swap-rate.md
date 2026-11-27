# Par swap rate from discount factors

For discount factors `D_t` (any real numbers) and payment dates `t = 1, …, T` with unit
accrual, the par swap rate is `(1 - D_T) / ∑_{t=1}^{T} D_t`, with the convention `x / 0 = 0`:
it is `0` when the annuity factor `∑_{t=1}^{T} D_t` is `0`, for instance when `T = 0`. When
`D_0 = 1` and the annuity factor is nonzero, it is the fixed rate at which the fixed and
floating legs have equal present values.
