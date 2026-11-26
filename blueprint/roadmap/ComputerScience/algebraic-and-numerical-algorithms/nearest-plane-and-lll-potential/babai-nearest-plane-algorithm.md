# Babai's nearest-plane algorithm

Given a basis $b_1, \dots, b_n$ with Gram-Schmidt vectors $b_j^*$ and a target $t$, **Babai's nearest-plane algorithm** sets $r = t$ and for $j = n, n-1, \dots, 1$ computes $c_j = \big\lfloor \langle r, b_j^* \rangle / \langle b_j^*, b_j^* \rangle \big\rceil$ (nearest integer) and replaces $r$ by $r - c_j b_j$; it outputs $y = t - r$, a vector of the integer span. Its output satisfies the **nearest-plane condition**: $|\langle b_j^*, t - y \rangle| \le \frac12 \|b_j^*\|^2$ for every $j$. With integer bases the computation can be carried out in exact rational arithmetic.

## Depends on

- [The Q factor of the Gram–Schmidt QR factorization](../../../LinearAlgebra/matrix-decompositions/qr-factorization/qr-q.md)

## Sources

- L. Babai, "On Lovász' Lattice Reduction and the Nearest Lattice Point Problem", Combinatorica 6(1), 1986.
- O. Regev, "Lattices in Computer Science", lecture notes, Tel Aviv University, 2004.
