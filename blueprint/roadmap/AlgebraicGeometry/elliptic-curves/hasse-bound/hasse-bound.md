# Hasse bound

Let $F$ be a finite field with $q$ elements and let $E$ be an elliptic curve over
$F$ given by a Weierstrass equation. If $N$ is the number of points of $E$ with coordinates in $F$,
including the point at infinity, then $(q + 1 - N)^2 \le 4q$ in $\mathbb{Z}$.

Proof: Manin's elementary polynomial-degree argument on a twist over the rational function field
$F(t)$, done separately for the odd-characteristic and characteristic-two normal forms. In
characteristic two the point count uses the fibres of the additive maps $y \mapsto y^2 + by$ with
$b \in F$, followed by the same projective neighboring-degree recurrence, as in
Chahal--Soomro--Top, *Rocky Mountain J. Math.* 44 (2014).

## Sources

- H. Hasse, J. Reine Angew. Math. 1936; modern Silverman, The Arithmetic of Elliptic Curves, 2nd ed.; Lean states integral squared form of |N-(q+1)| ≤ 2√q including point at infinity.
