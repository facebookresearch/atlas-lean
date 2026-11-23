# Asymptotic validity, lattice scores

Let `P` be a probability measure on `Ω` and `R` a
[lattice renewal input](../gumbel-limit-of-the-maximal-segment-score/lattice-renewal-input.md) with
span `h > 0` for the scores `X 0, X 1, …`: i.i.d. scores on the lattice `hℤ` satisfying the
[Cramér conditions](../gumbel-limit-of-the-maximal-segment-score/cramer-scores.md) with root
`θ > 0`, with the ladder decomposition (excursion heights on `hℤ`) and the lattice renewal tail
`P(Y ≥ (k + 1) h) ~ C e^{-θ (k + 1) h}` taken as hypotheses. If `C > 0`, the Karlin–Altschul p-value
`pₙ = 1 - exp(-K n e^{-θ Mₙ})` of the
[maximal segment score](../gumbel-limit-of-the-maximal-segment-score/max-segment-score-rv.md) `Mₙ`,
with the [constant `K = C / A`](../gumbel-limit-of-the-maximal-segment-score/k-2.md) (`A > 0` the
mean ladder-epoch length) of the lower lattice bound, is asymptotically conservative: for every
`α ∈ [0, 1]` and every `ε > 0`, eventually `P(pₙ ≤ α) ≤ α + ε`. Exact calibration does not follow:
for `C > 0`, `P(Mₙ ≤ log n / θ + x)`
[has no limit](../gumbel-limit-of-the-maximal-segment-score/not-tendsto.md).
