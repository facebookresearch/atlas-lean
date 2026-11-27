# Lambda-uniform spanning tree measures are strongly Rayleigh

Let $G=(V,E)$ be a connected graph on $n$ vertices and $\lambda \in \mathbb{R}_{> 0}^{E}$. Then $\mu_\lambda$, viewed as a measure on $2^E$, is an $(n-1)$-homogeneous strongly Rayleigh measure. In particular its generating polynomial is Lorentzian.

## Proof sketch

By the weighted matrix-tree theorem $g_{\mu_\lambda}(z)$ is proportional to $\det\big(\sum_{e}\lambda_e z_e\,b_e b_e^{\top}\big)$ restricted to the complement of one vertex coordinate, where $b_e$ is the signed incidence vector. A determinant $\det(\sum_i z_i A_i)$ with positive semidefinite $A_i$ is real stable (Borcea-Branden), and positive rescaling of variables preserves stability. Stable homogeneous polynomials with nonnegative coefficients are Lorentzian.

## Depends on

- [Maximum-entropy and lambda-uniform distributions over spanning trees](max-entropy-spanning-tree-distribution.md)
- [Strongly Rayleigh probability measures on subsets of a ground set](strongly-rayleigh-measure.md)
- [The set of Lorentzian polynomials](../../../Combinatorics/matroid-theory/lorentzian-polynomials/l.md)

## Proof depends on

- [Kirchhoff's matrix-tree theorem](../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/kirchhoff-matrix-tree.md)
- [Weighted matrix-tree theorem](../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/weighted-matrix-tree.md)
- [Stable polynomials are Lorentzian](../../../Combinatorics/matroid-theory/lorentzian-polynomials/stable-mem-l.md)
- [Real stable polynomials](../../../Algebra/zeros-of-polynomials/stable-polynomials/is-real-stable.md)

## Sources

- Julius Borcea, Petter Branden, Thomas M. Liggett, "Negative Dependence and the Geometry of Polynomials", Journal of the American Mathematical Society (2009), arXiv:0707.2340.
- Shayan Oveis Gharan, Amin Saberi, Mohit Singh, "A Randomized Rounding Approach to the Traveling Salesman Problem", FOCS (2011).
