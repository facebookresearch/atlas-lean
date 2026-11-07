# Total number of nonattacking anassas on the square board

For natural numbers $m$ and
$k$ and each $p$, let $A_S(m, k, p)$ be the number of nonattacking placements of $k$ anassas on
the square board $[1, m]^2$ with exactly $p$ of them strictly below the main diagonal, that is,
the number of $k$-element sets of squares $(i, j) \in [1, m]^2$ in which no two squares have
the same $i$ or the same $i - j$ and exactly $p$ squares satisfy $j < i$. Then, in $\mathbb{Q}$,

$$
\sum_{p=0}^{k} A_S(m, k, p) = \sum_{j=0}^{\lceil k/2 \rceil} (m-k+j)_j
\left\{ {m \atop m-k+j} \right\} 2^{k-2j} \left( \binom{k-j}{j-1} + \binom{k-j+1}{j} \right),
$$

where $(x)_j = x(x-1) \cdots (x-j+1)$ is the falling factorial, $\binom{k-j}{-1} = 0$, the power
$2^{k-2j}$ has an integer exponent, and $\left\{ {n \atop i} \right\}$ is Knuth's extension of
the Stirling numbers of the second kind to integer arguments; since $m \ge 0$, here it is the
ordinary Stirling number when $m - k + j \ge 0$ and $0$ otherwise.

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 13 (`jis-2025-25.8.6-thm-13`).
