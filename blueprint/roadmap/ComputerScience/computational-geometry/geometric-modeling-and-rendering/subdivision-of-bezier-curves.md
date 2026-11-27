# Subdivision of Bézier curves

Let $p$ be the Bézier curve with control points $c_0, \dots, c_n$ and let $c^r_i$ be the points of the de Casteljau triangle at parameter $s \in (0,1)$. Then $(c^0_0, c^1_0, \dots, c^n_0)$ is the control polygon of the curve $t \mapsto p(st)$, and $(c^n_0, c^{n-1}_1, \dots, c^0_n)$ is the control polygon of $t \mapsto p(s + (1 - s)t)$, both for $t \in [0,1]$.

## Proof depends on

- [The de Casteljau algorithm](the-de-casteljau-algorithm.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- M. S. Floater, *Lecture 8: Bézier curves*, lecture notes, University of Oslo
- G. Farin, *Curves and Surfaces for CAGD: A Practical Guide*, 5th ed., Morgan Kaufmann, 2002
