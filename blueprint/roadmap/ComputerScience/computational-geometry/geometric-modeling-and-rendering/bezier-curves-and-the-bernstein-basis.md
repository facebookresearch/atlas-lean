# Endpoint interpolation and convex-hull property of Bézier curves

For control points $c_0, \dots, c_n$ in a real vector space, the Bézier curve of degree $n$ is $p(t) = \sum_{i=0}^n c_i B^n_i(t)$, where $B^n_i(t) = \binom{n}{i} t^i (1-t)^{n-i}$ are the Bernstein polynomials of degree $n$. Then $p(0) = c_0$, $p(1) = c_n$, and $p(t)$ lies in the convex hull of the control points for every $t \in [0, 1]$; both follow from the facts that the Bernstein polynomials of degree $n$ are nonnegative on $[0,1]$, sum to $1$, and take the values $B^n_i(0) = [i = 0]$ and $B^n_i(1) = [i = n]$.

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- M. S. Floater, *Lecture 8: Bézier curves*, lecture notes, University of Oslo
- G. Farin, *Curves and Surfaces for CAGD: A Practical Guide*, 5th ed., Morgan Kaufmann, 2002
