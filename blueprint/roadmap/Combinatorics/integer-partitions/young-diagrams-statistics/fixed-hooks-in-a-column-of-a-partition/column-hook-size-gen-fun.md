# Generating function for column-$m$ hooks of size $k$

Let $n$, $m \ge 1$ and $k \ge 1$
be natural numbers. For a partition $\lambda$, write $\lambda_r$ for its $r$-th largest part
($0$ if it has fewer than $r$ parts), $\lambda'_m$ for the number of its parts that are at least
$m$, and $h_{r,m}(\lambda) = \lambda_r + \lambda'_m - r - m + 1$ for the hook length of the square
$(r, m)$. Let $H$ be the number of pairs $(\lambda, r)$ of a partition $\lambda$ of $n$ and a row
$1 \le r \le n$ with $m \le \lambda_r$ and $h_{r,m}(\lambda) = k$. In $\mathbb{Q}[[q]]$ write
$(a;q)_j = \prod_{i=0}^{j-1} (1 - a q^i)$ for $j \in \mathbb{N}$ and
$(a;q)_\infty = \prod_{i \ge 0} (1 - a q^i)$, so that $(q;q)_j = \prod_{i=1}^{j} (1 - q^i)$ and
$(q^m;q)_j = \prod_{i=0}^{j-1} (1 - q^{m+i})$, and let $P = \prod_{i=0}^{n} (1 - q^{k+i})^{-1}$.
Then $H$ is the coefficient of $q^n$ in

$$
P \sum_{l=1}^{k} \frac{q^{km - (l-1)(m-1)} (q^m;q)_{l-1}}{(q;q)_{l-1} (q;q)_{k-l}},
$$

and $H$ is also the coefficient of $q^n$ in

$$
q^{m+k-1} P \sum_{l=1}^{k} \frac{q^{(m-1)(k-l)} (q^m;q)_{l-1}}{(q;q)_{l-1} (q;q)_{k-l}}.
$$

$P$ is $1/(q^k;q)_\infty$ truncated after $n + 1$ factors, which changes no coefficient below
$q^{n+1}$; the exponent $km - (l-1)(m-1)$ is at least $k + m - 1$.

## Sources

- Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25 (2025), Article A28, Theorem 4.
