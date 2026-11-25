# Infinite dividend-discount identity from the finite identities

Let `0 < 1 + r`, and let `P t` and `D t` be the price and the dividend at date `t`. Suppose that
for every `n` the finite identity `P 0 = ∑_{t=1}^{n} D t / (1 + r)^t + P n / (1 + r)^n` holds,
that the discounted terminal price `P n / (1 + r)^n` tends to `0` as `n → ∞` (no bubble), and
that the dividends `D t`, `t ≥ 1`, are nonnegative. Then the series of discounted dividends
`∑_{t=1}^{∞} D t / (1 + r)^t` converges, with sum `P 0`, today's price. The finite identity is
taken as a hypothesis, so this is exactly the limit passage; it holds whenever prices satisfy the
one-period recursion `P t = (D (t+1) + P (t+1)) / (1 + r)`.
