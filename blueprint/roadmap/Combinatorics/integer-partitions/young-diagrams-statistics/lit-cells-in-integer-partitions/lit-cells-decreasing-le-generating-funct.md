# Lit cells of weakly decreasing partitions with few parts

Let $k$ and $s$ be natural
numbers with $s \le k$. Write $\binom{M}{m}_q$ for the Gaussian binomial coefficient, and $t[s, i]$
for the triangular $q$-binomial coefficient: the generating function of partitions with exactly
$i$ parts $x_1 \ge \cdots \ge x_i$ such that $x_j + j - 1 \le s$ for $1 \le j \le i$. Let
$\mathrm{lit}[k, s] \in \mathbb{Z}[[q]]$ be the power series whose coefficient of $q^n$ is the
number of partitions of $n$ with at most $s + 1$ parts and at most $k$ lit cells as weakly
decreasing bargraphs. Then

$$\mathrm{lit}[k, s] = \sum_{i=0}^{s} t[s, i] \, q^{i(k-s)} \binom{k + 1 - i}{k - s}_q.$$

## Sources

- Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer Partitions*, INTEGERS 24 (2024), Article A56, Proposition 5, eq. (13) (`integers-2024-A56-prop-5`).
