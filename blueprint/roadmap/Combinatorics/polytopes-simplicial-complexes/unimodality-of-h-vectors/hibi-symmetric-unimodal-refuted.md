# Hibi's conjecture on symmetric $h^*$-vectors is false

There are a natural number $d$, a
finite set $S \subseteq \mathbb{Z}^d$ whose convex hull $P \subseteq \mathbb{R}^d$ has nonempty
interior, and a polynomial $h = \sum_i h^*_i z^i \in \mathbb{Z}[z]$ that is an $h^*$-polynomial
of $P$, that is,

$$\Big(\sum_{t \ge 0} \#(tP \cap \mathbb{Z}^d)\, z^t\Big) (1 - z)^{d+1} = h(z)$$

as formal power series, such that $h^*_i = h^*_{d-i}$ for all $0 \le i \le d$ but $h$ is not
unimodal.

Mustaţă and Payne (Example 1.1) give a reflexive $6$-dimensional lattice polytope with
$h^*$-vector $(1, 6, 8, 6, 8, 6, 1)$, which is symmetric and not unimodal.

Payne's Example 4.2 with $b = 3$, $k = 2$, and $r = 0$ gives another counterexample. In the
lattice basis $e_1,\ldots,e_5,-f$, where $f = (e_1 + \cdots + e_6)/3$, it is the weighted simplex
with weights $(1,1,1,1,1,3)$ and
[$h^*$-vector $(1,1,2,1,2,1,1)$](hibi-weighted-simplex-h-star.md).

## Sources

- S. Payne, *Ehrhart series and lattice triangulations*, Discrete Comput. Geom. 40 (2008), 365–376, Example 4.2 and the proof of Theorem 1.4.
- C. A. Athanasiadis, On the unimodality of h*-vectors, in Ehrhart Quasipolynomials: Algebra, Combinatorics, and Geometry, Oberwolfach Reports 1 (2004), no. 39, p. 2078, Conjecture 2, DOI 10.4171/OWR/2004/39; resolution: M. Mustaţă and S. Payne, Ehrhart polynomials and stringy Betti numbers, Math. Ann. 333 (2005), 787-795, DOI 10.1007/s00208-005-0691-x, arXiv:math/0504486, Example 1.1: for f = (e1 + ... + e6)/3, N = ℤ⁶ + ℤ f and P the polytope with vertices e1, ..., e6, e1 - f, ..., e6 - f, P is reflexive with δ_P = (1, 6, 8, 6, 8, 6, 1), a counterexample to Hibi's conjecture for d = 6 (abstract: 'counterexamples to Hibi's conjecture on the unimodality of delta-vectors of reflexive polytopes'), https://arxiv.org/abs/math/0504486.
