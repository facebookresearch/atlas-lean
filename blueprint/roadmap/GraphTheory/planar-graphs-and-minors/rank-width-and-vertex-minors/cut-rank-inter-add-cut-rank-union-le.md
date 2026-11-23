# Cut-rank is submodular

For every finite graph $G$ and vertex sets $X, Y$,

$$\rho_G(X \cap Y) + \rho_G(X \cup Y) \le \rho_G(X) + \rho_G(Y).$$

The source deduces it from the submodular inequality for ranks of submatrices,
$\mathrm{rk}\,M[X_1, Y_1] + \mathrm{rk}\,M[X_2, Y_2] \ge \mathrm{rk}\,M[X_1 \cup X_2, Y_1 \cap Y_2] + \mathrm{rk}\,M[X_1 \cap X_2, Y_1 \cup Y_2]$
(its Proposition 6.1), applied to the adjacency matrix.

## Sources

- S. Oum and P. Seymour, *Approximating clique-width and branch-width*, J. Combin. Theory Ser. B 96 (2006) 514–528; read in the authors' preprint of 20 October 2004 (https://sangil.dimag.kr/pdf/rwdfpt.pdf), whose numbering is cited here, Corollary 6.2 (second statement) and Proposition 6.1.
- S. Oum, *Rank-width: algorithmic and structural results*, Discrete Appl. Math. 231 (2017) 15–24; read as arXiv:1601.03800v2 (27 July 2016), whose numbering is cited here, Section 2.1, inequality (2).
