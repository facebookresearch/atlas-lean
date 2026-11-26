# BM25 term scores are nonnegative and saturate

Let $\mathrm{idf} \ge 0$, $\mathrm{tf} \ge 0$ and $k_1 > 0$, and let the length-normalization factor $(1 - b) + b \cdot (\mathrm{docLen} / \mathrm{avgLen})$ be positive. Then the [BM25 term score](bm25-term-score.md) is nonnegative and at most $\mathrm{idf} \cdot (k_1 + 1)$.
