# Window event for distinct scores

Let $1 \le r \le m + 1$ and $a < b$, and let $\omega$ be a score vector with pairwise distinct scores. Then

$$\bigl( a = 0 \ \text{or}\ \tilde S_{(a)} \le S_{(r)} \bigr) \ \text{and}\ S_{(r)} \le \tilde S_{(b)} \iff a \le J < b,$$

that is $a + 1 \le K \le b$, where $S_{(r)}$ is the [$r$-th real order statistic](real-order-statistic.md),
$\tilde S_{(a)}$ the [$a$-th synthetic order statistic](synthetic-order-statistic.md), $J$ the [sample
rank](sample-rank.md) and $K = J + 1$; $a = 0$ stands for the $-\infty$ sentinel. Distinctness is needed
for the lower comparison: with a tie between $\tilde S_{(a)}$ and $S_{(r)}$ the event can hold while
$J < a$.
