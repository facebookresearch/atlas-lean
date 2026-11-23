# The Möbius series for pairwise non-coprime tuples equals the inclusion–exclusion sum

Let $k \ge 2$. For a $k$-tuple $n = (n_1, \dots, n_k)$ of positive integers let $\beta(n) = 1$
if the number of coprime pairs of $n$ is $0$, that is, if $\gcd(n_i, n_j) \ne 1$ for all
$1 \le i < j \le k$, and $\beta(n) = 0$ otherwise. Let
$(\mu * \beta)(n) = \sum_{d_1 \mid n_1, \dots, d_k \mid n_k} \mu(d_1) \cdots \mu(d_k)\,
\beta(n_1/d_1, \dots, n_k/d_k)$, where $\mu$ is the Möbius function. Then

$$
\sum_{n} \frac{(\mu * \beta)(n)}{n_1 \cdots n_k}
  = \sum_{j=0}^{k(k-1)/2} (-1)^j \sum_{|E| = j} A_E,
$$

where the left sum runs over all $k$-tuples $n$ of positive integers, the inner sum on the right
runs over all sets $E$ of $j$ pairs $(i, i')$ with $1 \le i < i' \le k$, and $A_E$ is the
coprimality density of the graph on $\{1, \dots, k\}$ with edge set $E$.

In the source the common value is the density $C_k$ of pairwise non-coprime $k$-tuples. The
asymptotic count of such tuples is the case $r = 0$ of the count of $k$-tuples with exactly $r$
coprime pairs.

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Corollary 12 (`jis-2024-24.8.5-cor-12`).
