# Present value of the floating leg of a swap

For a swap of notional 1 with payment dates `t = 1, …, T` and discount factors `D_t` (any real
numbers), the floating payment at date `t`, the forward rate over `[t - 1, t]`, is valued at
`D_{t-1} - D_t`, so the floating leg's present value is `∑_{t=1}^{T} (D_{t-1} - D_t)`.
