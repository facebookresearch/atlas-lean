# BM25 term scores are nondecreasing in term frequency

Let $\mathrm{idf} \ge 0$ and $k_1 > 0$, and let the length-normalization factor $(1 - b) + b \cdot (\mathrm{docLen} / \mathrm{avgLen})$ be positive. Then the [BM25 term score](bm25-term-score.md) is nondecreasing in $\mathrm{tf}$ on $\mathrm{tf} \ge 0$. The hypothesis $k_1 > 0$ is needed: with $\mathrm{idf} = 1$, $b = 0$ and $k_1 = -1/2$, the score is $0$ at $\mathrm{tf} = 0$ and $-1/2$ at $\mathrm{tf} = 1/4$.
