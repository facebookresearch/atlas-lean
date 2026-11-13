# Coverage of the Clopper–Pearson interval

If `X ~ Bin(n, p)` and `0 < α < 1`, then
`P(L(X) ≤ p ≤ U(X)) ≥ 1 - α`, for every `n` and every `p ∈ [0, 1]`.

Non-coverage means `p < L(X)` or `U(X) < p`; each event forces the corresponding exact tail
p-value below `α / 2`, which has probability at most `α / 2`.

## Sources

- Clopper–Pearson (1934); Casella–Berger (2002), §9.2.3.
