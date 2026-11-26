# Trunc Binom

The **zero-truncated binomial law**: the probability that an ascertained sibship of size `s`
has exactly `k` affected children, when each child is affected independently with probability
`p` and the sibship is ascertained if and only if `k ≥ 1`. It vanishes for `k = 0` and `k > s`.
For `1 ≤ k ≤ s` it is `C(s, k) p^k (1 - p)^(s - k) / (1 - (1 - p)^s)`. The intended domain is
`s ≥ 1` and `0 < p < 1`, where the denominator `1 - (1 - p)^s` is positive. Outside it the
denominator can vanish (e.g. `p = 0`), and then the value is `0`, since Lean's division is total
(`x / 0 = 0`).
