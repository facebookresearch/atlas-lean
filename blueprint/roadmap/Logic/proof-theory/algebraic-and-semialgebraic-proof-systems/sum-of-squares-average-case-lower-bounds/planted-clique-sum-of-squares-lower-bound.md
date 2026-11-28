# Sum-of-Squares lower bound for planted clique

There is an absolute constant $c$ such that for every degree $d = d(n)$ and large $n$, the degree-$d$ Sum-of-Squares relaxation of the clique problem on $G(n, 1/2)$ has integrality gap at least $n^{1/2 - c(d/\log n)^{1/2}}$; constant-degree SoS cannot certify that a random graph has no clique of size $n^{1/2 - o(1)}$.

For a graph $G$ on $[n]$ and parameters $d, \omega$, a **degree-$d$ pseudo-distribution** for the planted clique problem is a map $p \mapsto \tilde{\mathbb{E}}_G\, p$ on $n$-variate polynomials of degree at most $d$ such that:

1. (Linearity) $p \mapsto \tilde{\mathbb{E}}_G\, p$ is linear;
2. (Normalization) $\tilde{\mathbb{E}}_G\, 1 = 1$;
3. (Booleanity) $\tilde{\mathbb{E}}_G\, x_i^2 p = \tilde{\mathbb{E}}_G\, x_i p$ for every $p$ of degree at most $d - 2$ and $i \in [n]$;
4. (Clique constraint) $\tilde{\mathbb{E}}_G\, x_i x_j p = 0$ for every non-edge $\{i, j\}$ and $p$ of degree at most $d - 2$;
5. (Size constraint) $\tilde{\mathbb{E}}_G \sum_{i=1}^n x_i = \omega$;
6. (Positivity) $\tilde{\mathbb{E}}_G\, p^2 \ge 0$ for every $p$ of degree at most $d/2$.

**Theorem.** There is an absolute constant $c$ such that for every $d = d(n)$ and large enough $n$, the SoS relaxation of the planted clique problem has integrality gap at least $n^{1/2 - c(d/\log n)^{1/2}}$. Equivalently, there is a constant $c$ such that if $\omega \le n^{1/2 - c(d/\log n)^{1/2}}$, then with high probability over $G \sim G(n, 1/2)$ there is a degree-$d$ pseudo-distribution $\tilde{\mathbb{E}}_G$ satisfying constraints 1 to 6.

## Proof sketch

The bound is nearly tight, since polynomial-time algorithms find planted cliques of size $\epsilon\sqrt{n}$, and it improves the earlier degree-dependent bounds of Meka-Potechin-Wigderson, Deshpande-Montanari and Hopkins et al. Integrality gaps are negative results for the refutation variant (certifying that $G(n,1/2)$ has no $\omega$-clique) and also defeat the natural SoS algorithm for the decision variant. The pseudo-distribution is built from the truncated pseudo-calibrated moments; the clique constraints hold exactly, normalization and size hold up to factors $1 \pm n^{-\Omega(\epsilon)}$ before rescaling, and positivity is proved by approximately factoring the moment matrix through vertex separators of ribbons and bounding the norms of graphical matrices.

## Depends on

- [Planted clique model, search and detection problems](../../../../GraphTheory/random-graphs/planted-clique/planted-clique-model.md)
- [Sums-of-Squares proof system](../sums-of-squares-proof-system.md)

## Proof depends on

- [Pseudo-calibration](pseudo-calibration.md)

## Sources

- Boaz Barak, Samuel B. Hopkins, Jonathan A. Kelner, Pravesh K. Kothari, Ankur Moitra, Aaron Potechin, "A nearly tight sum-of-squares lower bound for the planted clique problem", *SIAM Journal on Computing* 48(2), 2019, https://doi.org/10.1137/17M1138236; numbering of arXiv:1604.03084v2 (Theorem 1.1, Definition 2.2, Theorem 2.3, Remark 1.2).
