# Marcus-Spielman-Srivastava: bipartite Ramanujan graphs of every degree and every size

For every $d \ge 3$ and every $n \ge 1$ there exists a $d$-regular bipartite Ramanujan (multi)graph with $n$ vertices on each side. It can be taken to be a union of $d$ perfect matchings between the two sides.

## Proof sketch

Take the union of $d$ independent uniformly random perfect matchings across the bipartition, with adjacency matrix $A = \sum_{i=1}^{d} (P_i \oplus S_i) M (P_i \oplus S_i)^{\mathsf T}$ for a fixed perfect matching $M$ and independent uniformly random $n \times n$ permutation matrices $P_i, S_i$. Its characteristic polynomial always has the trivial roots $\pm d$, and $d$ exceeds the Ramanujan threshold $2\sqrt{d-1}$ for $d > 2$, so the full characteristic polynomial cannot be compared with the threshold. Instead the trivial factor is stripped: by the asymmetric convolution identity,

$$
\mathbb{E}\, \det(xI - A) = (x^2 - d^2)\, \mathcal{S}\big[p \mathbin{+\!\!+}_{n-1} p \mathbin{+\!\!+}_{n-1} \cdots \mathbin{+\!\!+}_{n-1} p\big](x), \qquad p(x) = (x-1)^{n-1},
$$

with $d$ copies of $p$, where $\mathbin{+\!\!+}_{n-1}$ is the asymmetric additive convolution of degree-$(n-1)$ polynomials with nonnegative roots and $\mathcal{S}[q](x) = q(x^2)$. Uniform random permutations are products of independent random swaps, so the expected characteristic polynomials over partial choices form an interlacing family, and some outcome has second largest eigenvalue at most the largest root of the reduced polynomial $\mathcal{S}[p \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} p]$. The barrier bound for the asymmetric convolution, the analogue of the root bound for the symmetric finite free convolution, gives $K_{\mathcal{S}(p \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} p)}(w) \le d\, K_{\mathcal{S} p}(w) - (d-1)/w$, and minimizing over $w$ bounds that root by $2\sqrt{d-1}$. Since the graph is bipartite, its spectrum is symmetric and it is Ramanujan.

## Depends on

- [Ramanujan graphs and bipartite Ramanujan graphs](ramanujan-graphs-and-bipartite-ramanujan-graphs.md)

## Proof depends on

- [Finite free convolution preserves real-rootedness and obeys a root bound](finite-free-convolution-preserves-real-rootedness.md)
- [Common upper interlacing bounds some member's largest root by a weighted sum's](../../../Algebra/zeros-of-polynomials/interlacing-families-of-polynomials/exists-max-real-root-le-weighted-sum-of.md)

## Sources

- Adam W. Marcus, Daniel A. Spielman, Nikhil Srivastava, "Interlacing families IV: bipartite Ramanujan graphs of all sizes", SIAM Journal on Computing 47(6) (2018), FOCS (2015); arXiv:1505.08010 (Theorems 1.1, 2.8 and 3.4, Corollary 4.13).
- Adam W. Marcus, Daniel A. Spielman, Nikhil Srivastava, "Finite free convolutions of polynomials", Probability Theory and Related Fields 182 (2022); arXiv:1504.00350 (Theorem 1.8).
