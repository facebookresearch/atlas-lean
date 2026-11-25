# Window probability (i.i.d. atomless scores)

Let $m, N, r, a, b \in \mathbb{N}$ with $1 \le r \le m + 1$ and $a < b$, and let the scores be i.i.d. with
law $\nu$, a probability measure on $\mathbb{R}$ without atoms. With $F(t) = P(J + 1 \le t)$, $J$ the
[sample rank](../sample-rank-law/sample-rank.md),

$$P\bigl( (a = 0 \ \text{or}\ \tilde S_{(a)} \le S_{(r)}) \ \text{and}\ S_{(r)} \le \tilde S_{(b)} \bigr) = F(b) - F(a),$$

where $S_{(r)}$ is the [$r$-th real order statistic](real-order-statistic.md) and $\tilde S_{(a)}$ the
[$a$-th synthetic order statistic](synthetic-order-statistic.md). The window of interest is
$0 \le a < b \le N + 1$.
