# Asymptotic validity, nonlattice scores

Let `P` be a probability measure on `Ω` and `R` a
[nonlattice renewal input](../gumbel-limit-of-the-maximal-segment-score/nonlattice-renewal-input.md)
for the scores `X 0, X 1, …` (i.i.d. nonlattice scores satisfying the
[Cramér conditions](../gumbel-limit-of-the-maximal-segment-score/cramer-scores.md) with root
`θ > 0`, with the ladder decomposition and the renewal tail `P(Y > t) ~ C e^{-θ t}` taken as
hypotheses). If `C > 0`, then for every `α ∈ [0, 1]` and every `ε > 0`, eventually
`P(pₙ ≤ α) ≤ α + ε`, where `pₙ = 1 - exp(-K n e^{-θ Mₙ})` is the
[Karlin–Altschul p-value](gumbel-pvalue.md) of the
[maximal segment score](../gumbel-limit-of-the-maximal-segment-score/max-segment-score-rv.md) `Mₙ`
of the first `n` scores and `K = C / A` is the
[Gumbel constant](../gumbel-limit-of-the-maximal-segment-score/k.md), with `A > 0` the mean
ladder-epoch length.
