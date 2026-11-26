# Subdivision of the admissible IBD region by double-half-cousin separations

For $i, j \in \mathbb N_0$ let

$$v_{i,j} = \Bigl( (1 - 2^{-i})(1 - 2^{-j}),\; 2^{-i} 2^{-j} \Bigr)$$

in $(\kappa_0, \kappa_2)$ coordinates, with $v_{\infty, j} = v_{j, \infty} = (1 - 2^{-j}, 0)$ and $v_{\infty,\infty} = (1, 0)$, and let $V_{i,j}$ be the convex hull of $v_{i,j}, v_{i+1,j}, v_{i,j+1}, v_{i+1,j+1}$. For $m \ge n$ in $\mathbb N_0 \cup \{\infty\}$ let $A_{m,n}$ be the set of IBD points realized by double half cousins $\mathrm{DHC}^{f_1,f_2}_{m,n}$ as $f_1, f_2$ range over $[0, 1]$.

**Theorem** (Theorem 9 of the source). $A_{m,n}$ is the intersection of the admissible region with $V_{m,n}$. In particular the sets $A_{m,n}$ are closed and together subdivide the admissible region.

The IBD point of $\mathrm{DHC}^{f_1,f_2}_{m,n}$ is the bilinear interpolation

$$\kappa = f_1 f_2\, v_{m,n} + f_1 \bar f_2\, v_{m,n+1} + \bar f_1 f_2\, v_{m+1,n} + \bar f_1 \bar f_2\, v_{m+1,n+1}, \qquad \bar f_j = 1 - f_j. \tag{13}$$

## Depends on

- [Double half cousins with inbred founders realize every admissible IBD point](double-half-cousins-realize-admissible-ibd-coefficients.md)

## Proof depends on

- [Double half cousins with inbred founders realize every admissible IBD point](double-half-cousins-realize-admissible-ibd-coefficients.md)
- [Every kinship coefficient is realized by half cousins with an inbred founder](half-cousin-kinship-with-inbred-founder.md)

## Expansion

By Eq. (7) the fathers' kinship is $(1 + f_1)/2^{m+1} = f_1 2^{-m} + \bar f_1 2^{-(m+1)}$, affine in $f_1$, and similarly for the mothers. Substituting into $\kappa_0 = (1 - \phi_1)(1 - \phi_2)$ and $\kappa_2 = \phi_1\phi_2$ makes $\kappa$ bilinear in $(f_1, f_2)$ with corner values $v_{m,n}, \dots, v_{m+1,n+1}$, which gives (13) and $A_{m,n} \subseteq V_{m,n}$. The converse uses the explicit construction of the realization theorem to show the separations it produces for an admissible interior point of $V_{m,n}$ are $m$ and $n$ (Section 5.2).

## Sources

- M. D. Vigeland, Relatedness coefficients in pedigrees with inbred founders, Journal of Mathematical Biology 81 (2020), 185-207. <https://doi.org/10.1007/s00285-020-01505-x> (PMCID PMC7363742)
