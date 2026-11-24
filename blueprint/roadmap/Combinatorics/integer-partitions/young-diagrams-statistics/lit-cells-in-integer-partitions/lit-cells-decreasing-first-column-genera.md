# Lit cells when only the first column is lit

For a partition $p$ of $n$ with $\ell \ge 1$
parts $x_1 \ge x_2 \ge \cdots \ge x_\ell$, say that only the first column of its weakly
decreasing bargraph is lit when the number of lit cells of $p$ equals its largest part $x_1$,
that is, when $x_i + i - 1 \le x_1$ for $1 \le i \le \ell$. Let $F(q) \in \mathbb{Z}[[q]]$ be
the power series whose coefficient of $q^n$ is the sum of $x_1$ over the partitions of $n$ in
which only the first column is lit and $x_1 \ge 2$. For $r \ge 0$ let $T_q(r)$ be the
generating function of partitions contained in the triangle with column heights
$r, r - 1, \ldots, 1$. Then

$$F(q) = \sum_{r \ge 1} (r + 1) q^{r+1} T_q(r),$$

where the sum converges coefficientwise.

The condition $x_1 \ge 2$ is the range $r \ge 1$ of the paper's
$T(u, q) = \sum_{r \ge 1} u^{r+1} q^{r+1} T_q(r)$; among the partitions in which only the first
column is lit it excludes only $(1)$.

## Sources

- Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer Partitions*, INTEGERS 24 (2024), Article A56, Proposition 6.
