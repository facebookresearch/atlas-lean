# Cut-rank function

Let $G$ be a finite simple graph. For a vertex set $X$, the cut-rank $\rho_G(X)$ is the rank over
the two-element field $\mathrm{GF}(2)$ of the $X \times (V \setminus X)$ matrix whose $(x, y)$ entry is
$1$ when $x$ and $y$ are adjacent and $0$ otherwise. In particular
$\rho_G(\emptyset) = \rho_G(V) = 0$, and $\rho_G(\{v\}) \le 1$.

The cut-rank is symmetric and submodular, and rank-width is the branch-width of this function.

## Sources

- S. Oum and P. Seymour, *Approximating clique-width and branch-width*, J. Combin. Theory Ser. B 96 (2006) 514–528; read in the authors' preprint of 20 October 2004 (https://sangil.dimag.kr/pdf/rwdfpt.pdf), whose numbering is cited here, Definition 6.1.
- S. Oum, *Rank-width: algorithmic and structural results*, Discrete Appl. Math. 231 (2017) 15–24; read as arXiv:1601.03800v2 (27 July 2016), whose numbering is cited here, Section 2.1.
