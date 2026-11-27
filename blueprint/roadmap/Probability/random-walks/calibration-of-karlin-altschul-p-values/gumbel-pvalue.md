# Karlin–Altschul p-value of a maximal segment score

For real numbers `K`, `θ` and `s` and a natural number `n`, the Karlin–Altschul p-value of a score
`s` is `p = 1 - exp(-K n e^{-θ s})`: the Gumbel approximation of `P(Mₙ ≥ s)` for the
[maximal segment score](../gumbel-limit-of-the-maximal-segment-score/max-segment-score.md) `Mₙ` of
a score sequence of length `n`, with constant `K` and Cramér root `θ` (the `λ` of Karlin and
Altschul). It is defined for all real `K`, `θ` and `s`: it is at most `1`, positive when `K > 0`
and `n ≥ 1`, `0` when `K = 0` or `n = 0`, and negative when `K < 0` and `n ≥ 1`. The intended
domain is `K > 0`, `θ > 0` and `n ≥ 1`.
