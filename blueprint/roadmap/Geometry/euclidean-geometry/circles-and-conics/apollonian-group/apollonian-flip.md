# Apollonian flip

For $i \in \{1, 2, 3, 4\}$, the flip $S_i$ replaces the $i$-th entry of a quadruple by twice the sum of the
other three entries minus itself:

$$S_i(v)_i = 2 \sum_{j \ne i} v_j - v_i, \qquad S_i(v)_j = v_j \ (j \ne i).$$

On the curvatures of a Descartes configuration, $S_i$ replaces the $i$-th circle by the other circle tangent to the
remaining three. $S_i$ is multiplication by the matrix that agrees with the identity except in row $i$, which is
$(2, 2, 2, 2)$ with $-1$ in position $i$; these are the generators $S_1, \dots, S_4$ of the Apollonian group.

## Related topics

- [Apollonian generator $S_1$ in the local-global statements](../../../../NumberTheory/arithmetic-geometry/local-global-conjecture-for-apollonian-circle-pa/s.md):
  the same matrix, defined over $\mathbb{Z}$ for the Haag–Kertzer–Rickards–Stange statements.

## Sources

- A. Kontorovich and H. Oh, *Apollonian circle packings and closed horospheres on hyperbolic 3-manifolds*, J. Amer. Math. Soc. 24 (2011) 603–648, arXiv:0811.2236v5, equation (1.3) and the matrices $S_1, \dots, S_4$ of the introduction.
- J. C. Lagarias, C. L. Mallows and A. R. Wilks, *Beyond the Descartes circle theorem*, Amer. Math. Monthly 109 (2002) 338–361, arXiv:math/0101066v1, equation (2.1).
