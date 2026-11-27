# Ladder input for a maximal-segment-type statistic

For a measure `P` on `Ω` and real statistics `M n : Ω → ℝ` (`n = 0, 1, …`), a ladder input
consists of excursion heights `Y i : Ω → ℝ`, counts `N n : Ω → ℕ` of the excursions completed by
time `n`, a function `F : ℝ → ℝ` and a real number `A > 0`, the mean excursion length, such that:

- each `Y i` is measurable, the `Y i` are independent under `P` (which forces `P` to be a
  probability measure), and `P(Y i ≤ t) = F(t)` for every `i` and every real `t`;
- `N n / n → 1 / A` in probability: `P(|N n / n - 1 / A| ≥ ε) → 0` for every `ε > 0`;
- `P`-almost surely, for every `n`, `Y i ≤ M n` for every `i < N n`, and `M n ≤ t` for every real
  `t` with `Y i ≤ t` for all `i ≤ N n`.

It records the regenerative structure that the descending ladder epochs of a score walk provide
for its [maximal segment score](max-segment-score-rv.md). The limit theorems take it as a
hypothesis; for scores satisfying the [Cramér conditions](cramer-scores.md) such an input is
[constructed from the scores](to-ladder-input.md).
