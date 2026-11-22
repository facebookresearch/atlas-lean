# Erdős Problem 1076 fails as worded

For $k, n \in \mathbb{N}$ let $\mathcal{F}_k$ be the family
of $3$-graphs with $k$ vertices and $k - 2$ edges, and let $\mathrm{ex}_3(n, \mathcal{F}_k)$ be the
largest number of triples in a $3$-uniform hypergraph on $n$ vertices that contains no member of
$\mathcal{F}_k$, that is, in which no $k$ vertices span $k - 2$ or more triples. It is not true
that for every $k \ge 5$, $\mathrm{ex}_3(n, \mathcal{F}_k) / n^2 \to 1/6$ as $n \to \infty$.

Already $k = 5$ fails: Glock proved that the largest triple system on $n$ vertices with no five
vertices spanning three triples has $(1 + o(1)) n^2 / 5$ triples, so
$\mathrm{ex}_3(n, \mathcal{F}_5) / n^2 \to 1/5$; his §1 states this as the answer to whether $1/6$
is sharp for every $k$.

## Sources

- T. F. Bloom, Erdős Problems, Problem #1076, https://www.erdosproblems.com/1076 (status PROVED); resolution: S. Glock, Triple systems with no three triples spanning at most five points, Bull. Lond. Math. Soc. 51 (2019), 230-236, abstract and Theorem 2: lim n⁻² f⁽³⁾(n; 5, 3) = 1/5, where f⁽³⁾(n; k, s) is the largest number of triples on n points containing no k points spanning s triples; §1 poses the question whether the lower bound lim inf n⁻² f⁽³⁾(n; k, k - 2) ≥ 1/6 is sharp in general, and Theorem 2 shows it is not for k = 5 (arXiv:1809.02100), https://arxiv.org/abs/1809.02100.
