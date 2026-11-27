# Pair sum as cross-correlation of cell totals

Let $S$ be a finite set of SNPs with grid cells $c : S \to \mathbb{N}$ and let $K$ be a natural number with $c(x) < K$ for every $x$. Then for all $u, v : S \to \mathbb{R}$ and $j \in \mathbb{N}$,

$$\Pi_j(u, v) = \sum_{k=0}^{K-1} U_k\, V_{k+j},$$

where $\Pi_j$ is the [pair sum](pair-sum.md) and $U, V$ are the [cell totals](cell-sum.md) of $u$ and $v$.
