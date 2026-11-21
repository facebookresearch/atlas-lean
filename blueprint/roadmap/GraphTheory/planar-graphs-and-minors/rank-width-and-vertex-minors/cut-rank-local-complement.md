# Local complementation preserves the cut-rank function

For every finite simple graph $G$, every vertex $v$ and every vertex set $X$,

$$\rho_{G * v}(X) = \rho_G(X).$$

The proof follows the source. By symmetry of cut-rank we may assume $v \in X$. Then the cut matrix
of $G * v$ is obtained from that of $G$ by adding the row of $v$ to the rows of the neighbours of
$v$ in $X$; this is left multiplication by an invertible matrix (it squares to the identity over
$\mathrm{GF}(2)$), so the rank does not change. The source calls this observation fundamental: it
is what makes vertex-minors the right containment relation for rank-width.

## Sources

- S. Oum, *Rank-width and vertex-minors*, J. Combin. Theory Ser. B 95 (2005) 79–100; read in the author's revised preprint of 18 April 2005 (https://sangil.dimag.kr/pdf/vertexminor-revision.pdf), whose numbering is cited here, Proposition 2.6.
- S. Oum, *Rank-width: algorithmic and structural results*, Discrete Appl. Math. 231 (2017) 15–24; read as arXiv:1601.03800v2 (27 July 2016), whose numbering is cited here, Section 4.1.
