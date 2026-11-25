# Window probability for scores without ties

Let $m, N, r, a, b \in \mathbb{N}$ with $1 \le r \le m + 1$ and $a < b$, and let $\mu$ be a probability
measure on the score space under which the scores are almost surely pairwise distinct (no
exchangeability is needed). With $F(t) = \mu(J + 1 \le t)$, $J$ the [sample rank](../sample-rank-law/sample-rank.md),

$$\mu\bigl( (a = 0 \ \text{or}\ \tilde S_{(a)} \le S_{(r)}) \ \text{and}\ S_{(r)} \le \tilde S_{(b)} \bigr) = F(b) - F(a),$$

where $S_{(r)}$ is the [$r$-th real order statistic](real-order-statistic.md) and $\tilde S_{(a)}$ the
[$a$-th synthetic order statistic](synthetic-order-statistic.md). Here $a = 0$ plays the role of the
$-\infty$ sentinel, and $\tilde S_{(N+1)} = +\infty$ ([statement](synthetic-order-statistic-succ-eq-top.md)).
The underlying event identity holds only on the event of distinct scores.
