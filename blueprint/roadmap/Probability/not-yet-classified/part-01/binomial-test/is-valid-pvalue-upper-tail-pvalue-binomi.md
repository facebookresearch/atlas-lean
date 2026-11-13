# Exact binomial test of the composite one-sided null `p ≤ p₀`

If `X ~ Bin(n, p)` with
`p ≤ p₀`, the exact upper-tail p-value computed under the boundary null `Bin(n, p₀)` is valid:
`μ {upperTail Bin(n, p₀) X ≤ s} ≤ s` for every `s ∈ [0, 1]`.

The proof combines the boundary p-value with `monotoneOn_binomTail`, the monotonicity of the
binomial upper tail in the success probability.

## Sources

- Lehmann–Romano (2005), Lemma 3.3.1; Feller (1968) (binomial tails).
