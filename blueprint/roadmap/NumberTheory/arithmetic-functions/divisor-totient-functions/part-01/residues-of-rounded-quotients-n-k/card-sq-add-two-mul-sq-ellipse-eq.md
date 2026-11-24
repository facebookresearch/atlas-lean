# Lattice points in the ellipse $x^2 + 2y^2 \le n$

For a natural number $n$, let $F(n)$ be
the number of pairs $(x, y) \in \mathbb{Z}^2$ with $x^2 + 2y^2 \le n$, and let
$\mathcal{N}_{N,\alpha,\nu,r,m}$ be the number of $k \in \{1, \dots, N\}$ with
$\lfloor (N - \nu)/k + \alpha \rfloor \equiv r \pmod m$. Then $F(0) = 1$, $F(1) = 3$,
$F(2) = 5$ and $F(5) = 11$. For every natural number $n \notin \{1, 2, 5\}$, writing
$N = \lceil n/4 \rceil$ and $\theta = \{-n/4\}$ for the fractional part of $-n/4$,
$F(n) = 1 + 2\,\mathcal{N}_{N,3/4,\theta,1,2} + 2\,\mathcal{N}_{N,1/4,\theta,1,2} +
2n + 2\lfloor n/3 \rfloor - 4N$. This formula includes $n = 0$, where both sides are $1$.

## Sources

- Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024), Article 24.2.5, Corollary 49 (`jis-2024-24.2.5-cor-49`).
