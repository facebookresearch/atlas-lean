# Present value of a finite cash-flow stream

Present value of the finite cash-flow stream `f 0, f 1, …, f (T - 1)` discounted at
the per-period interest rate `r`: `∑_{t < T} f t / (1 + r) ^ t`. The economic model takes
`-1 < r`. At `r = -1` the convention `a / 0 = 0` makes every term after period `0`
vanish, so the value is not a present value there; the education investment rules are identities
that hold for every `r`, and so carry no rate hypothesis.

This is the same value as
[Present value under given discount factors](../../interest-theory-and-fixed-income/present-value-of-dated-cash-flows/present-value.md)
with the dates `0, …, T - 1` and the discount factors `((1 + r) ^ t)⁻¹`, for every `r` (both give
`0` for the terms with `(1 + r) ^ t = 0`).
