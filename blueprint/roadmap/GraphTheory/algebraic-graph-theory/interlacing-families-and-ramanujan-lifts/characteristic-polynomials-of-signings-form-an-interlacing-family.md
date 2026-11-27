# Characteristic polynomials of signings form an interlacing family

Order the edges $e_1, \dots, e_m$ of $G$. For a partial signing $\sigma \in \{\pm1\}^j$ let $f_\sigma(x) = \mathbb{E}\big[\det(xI - A_s) \mid s(e_i) = \sigma_i,\ i \le j\big]$, the expectation over uniformly random signs of the remaining edges. Then for every $j$ and $\sigma \in \{\pm1\}^{j}$, the two polynomials $f_{(\sigma, +1)}$ and $f_{(\sigma, -1)}$ have a common interlacing; equivalently every convex combination of them is real-rooted. Hence $\{\det(xI - A_s)\}_s$ is an interlacing family.

## Proof sketch

For a $d$-regular graph, $dI + A_s = \sum_{e = \{u,v\}} r_e r_e^{T}$ with $r_e = \chi_u + s_e \chi_v$, so $\det(xI - A_s) = \det\big((x + d)I - \sum_e r_e r_e^T\big)$ with independent random rank-one terms. The conditional expectations are therefore mixed characteristic polynomials of independent random rank-one positive semidefinite matrices (with arbitrary fixed values on the conditioned edges), which are real-rooted because they arise from real stable multivariate polynomials by derivatives and specialization. Real-rootedness of all convex combinations is equivalent to a common interlacing.

## Depends on

- [Common upper interlacing point](../../../Algebra/zeros-of-polynomials/interlacing-families-of-polynomials/has-common-upper-interlacing.md)
- [Two-lifts and signings of a graph](two-lifts-and-signings-of-graphs.md)

## Proof depends on

- [The expected characteristic polynomial of a random signing is the matching polynomial](expected-characteristic-polynomial-of-a-random-signing.md)
- [Mixed characteristic polynomial](../../../Analysis/operator-algebras/kadison-singer-problem/mixed-characteristic-polynomial.md)
- [Real stable polynomials](../../../Algebra/zeros-of-polynomials/stable-polynomials/is-real-stable.md)

## Sources

- Adam W. Marcus, Daniel A. Spielman, Nikhil Srivastava, "Interlacing families I: bipartite Ramanujan graphs of all degrees", Annals of Mathematics 182(1) (2015); arXiv:1304.4132.
