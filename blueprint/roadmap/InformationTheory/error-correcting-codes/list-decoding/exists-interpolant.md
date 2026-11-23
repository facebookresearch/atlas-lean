# Guruswami–Sudan interpolation step

Let $F$ be a field, $(\alpha_1, y_1), \dots, (\alpha_n, y_n) \in F^2$, and $w, D, r$ natural
numbers. If the number of monomials $X^i Y^j$ with $i, j \le D$ and $i + w j \le D$ exceeds
$n \cdot r(r+1)/2$, there is a nonzero $Q \in F[X][Y]$ of
[$(1, w)$-weighted degree](weighted-deg-le.md) at most $D$ with a
[root of multiplicity](has-root-mult.md) at least $r$ at every point $(\alpha_i, y_i)$.

This is the correctness of Step 1 of Algorithm 12.2.3 in Guruswami, Rudra and Sudan. The
coefficients of the monomials of $(1, w)$-degree at most $D$ are the unknowns; for each point the
coefficients of $X^u Y^v$, $u + v < r$, in the [translate](shift.md) $Q(X + \alpha_i, Y + y_i)$
are $\binom{r+1}{2}$ [linear constraints](card-low-monomials.md) (Lemma 12.2.10) whose vanishing
gives the [multiplicity](has-root-mult-of-coeff.md); a homogeneous linear system with more
unknowns than equations has a nonzero solution. (The bound $i, j \le D$ loses nothing when
$w \ge 1$.)

## Informally uses

- [Number of multiplicity constraints](card-low-monomials.md): Lemma 12.2.10.

## Background

- [Multiplicity from the translated coefficients](has-root-mult-of-coeff.md): why the vanishing of the low-degree translated coefficients gives the multiplicity in the ideal formulation used here.

## Sources

- V. Guruswami, M. Sudan, "Improved decoding of Reed–Solomon and algebraic-geometry codes", *IEEE Transactions on Information Theory* 45(6) (1999), 1757–1767.
- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Algorithm 12.2.3, Lemma 12.2.10 and the analysis of Step 1 before Theorem 12.2.12.
