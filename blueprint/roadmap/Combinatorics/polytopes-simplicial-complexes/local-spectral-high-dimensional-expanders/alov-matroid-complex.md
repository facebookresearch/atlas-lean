# Matroid independence complexes are 0-local spectral expanders

Let $M$ be a matroid of rank $r$ on a finite ground set and let $X_M$ be its independence complex, the pure $(r-1)$-dimensional complex whose top faces are the bases of $M$, weighted uniformly on bases. Then every link of every face of dimension at most $r-3$ in $X_M$ has nonpositive second eigenvalue, that is, $X_M$ is a one-sided $0$-local spectral expander. Consequently, the down-up walk on bases (the bases-exchange walk) has spectral gap at least $1/r$ and mixes in time $O(r \log(r\, |B(M)|))$ from any start, which yields a fully polynomial randomized approximation scheme for the number of bases of any matroid given by an independence oracle and proves the Mihail–Vazirani conjecture that the graph of the bases polytope of every matroid has edge expansion at least $1$.

## Proof sketch

Links of an independence complex are independence complexes of contractions, so it suffices to treat the $1$-skeleton of a rank-$2$-truncated link. Its adjacency matrix has at most one positive eigenvalue precisely when the bases generating polynomial is log-concave on the positive orthant restricted to the corresponding quadratic form, and matroid basis generating polynomials are completely log-concave. The spectral gap then follows from the trickling-down argument with $\lambda = 0$ or directly from the Alev–Lau product, and approximate counting follows from rapid mixing by the standard self-reducibility argument.

## Depends on

- [Local spectral expanders (one-sided and two-sided)](local-spectral-expander.md)
- [Up-down and down-up random walks on a weighted complex](up-down-walks.md)
- [Link of a face in a weighted complex](link-of-face.md)

## Proof depends on

- [Alev–Lau local-to-global bound for the down-up walk](alev-lau-local-to-global.md)

## Sources

- N. Anari, K. Liu, S. Oveis Gharan, C. Vinzant, "Log-concave polynomials II: high-dimensional walks and an FPRAS for counting bases of a matroid", STOC (2019); Annals of Mathematics 199 (2024), arXiv:1811.01816.
- V. L. Alev, L. C. Lau, "Improved analysis of higher order random walks and applications", STOC (2020), arXiv:2001.02827.
