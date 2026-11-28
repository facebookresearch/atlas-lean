# Finite dividend-discount identity

Let `r` be a real rate with `1 + r ≠ 0`, and let `P t` and `D t` be the price and the dividend
at date `t = 0, 1, 2, …`. If prices satisfy the one-period recursion
`P t = (D (t+1) + P (t+1)) / (1 + r)` for every `t` (price = discounted next dividend plus next
price), then for every `n`
`P 0 = ∑_{t=1}^{n} D t / (1 + r)^t + P n / (1 + r)^n`: today's price is the present value of the
next `n` dividends plus the discounted terminal price `P n`. Only the dividends at dates `t ≥ 1`
enter; at `n = 0` both sides are `P 0`.
