# The list has at most $D / w$ polynomials

Let $Q \in F[X][Y]$ be nonzero with [$(1, w)$-weighted degree](weighted-deg-le.md) at most $D$,
where $w \ge 1$. At most $D / w$ (integer division) polynomials $P \in F[X]$ have $Y - P(X)$
dividing $Q$: each such $P$ is a root of $Q$ viewed as a polynomial in $Y$ over the integral domain
$F[X]$, and $Q$ has $Y$-degree at most $D / w$. This bounds the size of the list output by the
[Guruswami–Sudan decoder](exists-interpolant-dvd.md).

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Section 12.2 (Algorithm 12.2.3, Step 3).
