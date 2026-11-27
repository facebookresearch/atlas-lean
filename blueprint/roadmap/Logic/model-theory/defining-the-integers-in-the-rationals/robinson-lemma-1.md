# Robinson's Lemma 1: rational values of $X^2 + Y^2 - pZ^2$ for $p \equiv 3 \pmod 4$

Let $p$ be a prime with $p \equiv 3 \pmod 4$ and let $M$ be a nonzero rational number. Then
$X^2 + Y^2 - pZ^2 = M$ has a solution in rational numbers $X, Y, Z$ if and only if $M$ is of
neither of the following forms, where $k$ is an integer and $S$ a rational number:

- $M = p \cdot k \cdot S^2$ with $\left(\frac{k}{p}\right) = 1$;
- $M = k \cdot S^2$ with $k \equiv p \pmod 8$.

Here $\left(\frac{k}{p}\right)$ is the Legendre symbol, so the first form requires $p \nmid k$, and
the second requires $k$ odd. Robinson writes capital letters for rationals and small letters for
integers (p. 106), which fixes the ranges of $k$ and $S$. Equivalently, $M$ is excluded exactly when
$M \in p \, (\mathbb{Q}_p^\times)^2$ or $M \in p \, (\mathbb{Q}_2^\times)^2$.

Robinson states the lemma without proof, as a special case of a general theorem of Hasse giving
necessary and sufficient conditions for the rational representation of a rational number by a
quadratic form. The form $f = \langle 1, 1, -p \rangle$ has
discriminant $d = -p$. By the
[Hasse–Minkowski theorem](../../../NumberTheory/quadratic-forms-sums-of-squares/hasse-minkowski-representation.md),
$f$ represents $M$ over $\mathbb{Q}$ if and only if it does over $\mathbb{R}$ and over every
$\mathbb{Q}_\ell$. Over $\mathbb{R}$, $f$ is indefinite and so isotropic; at an odd prime
$\ell \neq p$ its coefficients are $\ell$-adic units, so it is isotropic; at $\ell = p$ and
$\ell = 2$ it is anisotropic, since $(-1, p)_p = \left(\frac{-1}{p}\right) = -1$ and
$(-1, p)_2 = (-1)^{\varepsilon(-1)\varepsilon(p)} = -1$ by the formula for the Hilbert symbol. By the
local criterion for ternary forms, $f$ then represents $M$ over $\mathbb{Q}_\ell$ for
$\ell \in \{2, p\}$ exactly when $M \notin -d \, (\mathbb{Q}_\ell^\times)^2 = p \, (\mathbb{Q}_\ell^\times)^2$.
The description of the squares of $\mathbb{Q}_p$ (for odd $p$, a unit of $\mathbb{Z}_p$ is a square
exactly when its residue is a square modulo $p$; a unit of $\mathbb{Z}_2$ is a square exactly when it
is $\equiv 1 \pmod 8$) turns these two conditions into the two forms above.

## Sources

- J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
  98–114, <https://doi.org/10.2307/2266510>: Lemma 1, p. 107, with the remark before it that Lemmas
  1 and 2 are special cases of a general theorem of Hasse; the convention on capital and small
  letters, p. 106.
- H. Hasse, "Über die Darstellbarkeit von Zahlen durch quadratische Formen im Körper der rationalen
  Zahlen", *J. Reine Angew. Math.* 152 (1923), 129–148, as cited by J. Robinson (reference [5], p. 114):
  the general theorem of which, by Robinson, p. 107, Lemmas 1 and 2 are special cases.
- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973: Chapter II, §3 (the
  multiplicative group of $\mathbb{Q}_p$), pp. 15–19; Chapter III, §1 (local properties of the Hilbert
  symbol), pp. 19–23; Chapter IV, §2 (quadratic forms over $\mathbb{Q}_p$), pp. 35–41, and §3.2 (the
  Hasse–Minkowski theorem).
