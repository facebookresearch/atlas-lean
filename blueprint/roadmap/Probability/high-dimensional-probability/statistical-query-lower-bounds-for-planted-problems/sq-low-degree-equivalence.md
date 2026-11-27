# Statistical query algorithms and low-degree tests are almost equivalent

Consider testing a null distribution $Q$ against a family $\{P_u\}$ of planted distributions on $\mathbb{R}^N$ from $m$ i.i.d. samples, and the associated $m$-sample testing problem in which $\mathbb{P}$ draws a hidden $u$ and then $m$ samples from $P_u$. Under mild conditions on the problem (satisfied for instance when the family is closed under a symmetry group acting transitively, and for natural noise models): if the statistical dimension with average correlation of order $1/m$ is at least $q$ (which forces every statistical query algorithm with queries to VSTAT$(\Theta(m))$ to make at least $q$ queries), then the $m$-sample problem has bounded low-degree advantage at degree roughly $\log q / \log m$ (in an appropriate sense); and conversely, if the low-degree advantage at degree $D$ is bounded, then statistical query algorithms with VSTAT$(\tilde\Omega(m))$ need $q \ge m^{\Omega(D)}$ queries. As corollaries, there are new statistical query lower bounds for sparse PCA, tensor PCA and several variants of planted clique, matching the low-degree predictions.

## Proof sketch

A statistical query of $m$-sample tolerance corresponds to a low-degree polynomial in the $m$ samples, namely the empirical mean of the query, and the statistical dimension controls the second moment of the likelihood ratio of the $m$-sample problem restricted to polynomials that are sums over samples of degree-$D$ products. Conversely, low-degree advantage decomposes over subsets of samples, and a bound on the pairwise correlations $\chi_Q(P_u, P_{u'})$ in terms of the low-degree advantage, together with symmetry to pass from averages to most pairs, yields large statistical dimension.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](../low-degree-likelihood-ratio-method/low-degree-likelihood-ratio.md)
- [VSTAT oracle and statistical dimension with average correlation](vstat-oracle-statistical-dimension.md)

## Proof depends on

- [Statistical dimension lower bounds statistical query complexity](statistical-dimension-query-lower-bound.md)
- [Low-degree threshold of the spiked Wigner model](../low-degree-likelihood-ratio-method/spiked-wigner-low-degree-threshold.md)

## Sources

- M. Brennan, G. Bresler, S. B. Hopkins, J. Li, T. Schramm, "Statistical Query Algorithms and Low-Degree Tests Are Almost Equivalent", COLT (2021), arXiv:2009.06107.
