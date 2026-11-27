# The de Casteljau algorithm

For control points $c_0, \dots, c_n$ and $t \in \mathbb{R}$, set $c^0_i = c_i$ and $c^r_i = (1 - t) c^{r-1}_i + t c^{r-1}_{i+1}$ for $1 \le r \le n$ and $0 \le i \le n - r$. Then $c^n_0 = p(t)$, the value at $t$ of the Bézier curve of $c_0, \dots, c_n$; more generally $c^r_i$ is the value at $t$ of the Bézier curve of $c_i, \dots, c_{i+r}$. The computation uses $n(n+1)/2$ affine combinations.

## Depends on

- [Endpoint interpolation and convex-hull property of Bézier curves](bezier-curves-and-the-bernstein-basis.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- M. S. Floater, *Lecture 8: Bézier curves*, lecture notes, University of Oslo
