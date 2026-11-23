# Exact asymptotic calibration, nonlattice scores

Let `P` be a probability measure on `Ω` and `R` a
[nonlattice renewal input](../gumbel-limit-of-the-maximal-segment-score/nonlattice-renewal-input.md)
for the scores `X 0, X 1, …`: i.i.d. nonlattice scores satisfying the
[Cramér conditions](../gumbel-limit-of-the-maximal-segment-score/cramer-scores.md) with root
`θ > 0` (negative mean, `E e^{θ X} = 1`), with the ladder decomposition of the maximal segment
score and the renewal tail `P(Y > t) ~ C e^{-θ t}` of the excursion heights taken as hypotheses.
If `C > 0`, then for every `α ∈ [0, 1]`, `P(pₙ ≤ α) → α` as `n → ∞`, where
`pₙ = 1 - exp(-K n e^{-θ Mₙ})` is the [Karlin–Altschul p-value](gumbel-pvalue.md) of the
[maximal segment score](../gumbel-limit-of-the-maximal-segment-score/max-segment-score-rv.md) `Mₙ`
of the first `n` scores and `K = C / A` is the
[Gumbel constant](../gumbel-limit-of-the-maximal-segment-score/k.md), with `A > 0` the mean
ladder-epoch length (Karlin–Altschul 1990, with the limit of Iglehart and of Karlin and Dembo).
