# Finite dividend-discount identity

If prices satisfy the one-period recursion
`P t = (D (t+1) + P (t+1)) / (1 + r)` (source clause: "price = discounted next dividend
plus next price"), then today's price is the present value of the next `n` dividends plus
the discounted terminal price `P n`. `D t` is the dividend at date `t`; only `D t` for
`t ≥ 1` enter (the `Finset.Icc 1 n` sum). At `n = 0` both sides are `P 0`.
