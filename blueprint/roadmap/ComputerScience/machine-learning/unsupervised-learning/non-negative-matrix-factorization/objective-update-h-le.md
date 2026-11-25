# Lee–Seung, $H$ step

**Lee–Seung, $H$ step** (Lee and Seung 2001, Theorem 1): let $m, n, k$ be finite index sets,
$X \in \mathbb{R}^{m \times n}$, and $W \in \mathbb{R}^{m \times k}$, $H \in \mathbb{R}^{k \times n}$
with $W, H \ge 0$ entrywise. The [multiplicative update of $H$](update-h.md) does not increase
$\|X - W H\|_F^2$. The proof is the auxiliary-function argument: the quadratic term of the exact
expansion is bounded by Lee and Seung's diagonal majorant (here through a weighted
Cauchy–Schwarz inequality), and the update minimizes the majorant. $X$ may have any sign.
