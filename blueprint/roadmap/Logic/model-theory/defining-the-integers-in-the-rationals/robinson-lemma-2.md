# Robinson's Lemma 2: rational values of $X^2 + qY^2 - pZ^2$

Let $p$ and $q$ be odd primes with $p \equiv 1 \pmod 4$ and $\left(\frac{q}{p}\right) = -1$, and
let $M$ be a nonzero rational number. Then $X^2 + qY^2 - pZ^2 = M$ has a solution in rational
numbers $X, Y, Z$ if and only if $M$ is of neither of the following forms, where $k$ is an integer
and $S$ a rational number:

- $M = p \cdot k \cdot S^2$ with $\left(\frac{k}{p}\right) = -1$;
- $M = q \cdot k \cdot S^2$ with $\left(\frac{k}{q}\right) = -1$.

(That $p$ is odd follows from $p \equiv 1 \pmod 4$.)

Here $\left(\frac{\cdot}{\cdot}\right)$ is the Legendre symbol, so the forms require $p \nmid k$
and $q \nmid k$ respectively; the hypothesis $\left(\frac{q}{p}\right) = -1$ gives $q \neq p$.
Robinson writes capital letters for rationals and small letters for integers (p. 106).
Equivalently, $M$ is excluded exactly when $M \in pq \, (\mathbb{Q}_p^\times)^2$ or
$M \in pq \, (\mathbb{Q}_q^\times)^2$.

Robinson states the lemma without proof, as a special case of the same theorem of Hasse. The form
$f = \langle 1, q, -p \rangle$ has discriminant $d = -pq$, and it is isotropic over a field exactly
when the Hilbert symbol $(-q, p)$ is $1$. By the
[Hasse–Minkowski theorem](../../../NumberTheory/quadratic-forms-sums-of-squares/hasse-minkowski-representation.md),
$f$ represents $M$ over $\mathbb{Q}$ if and only if it does over $\mathbb{R}$ and over every
$\mathbb{Q}_\ell$. Over $\mathbb{R}$, $f$ is indefinite; at an odd prime $\ell \notin \{p, q\}$ its
coefficients are units; and $(-q, p)_2 = (-1)^{\varepsilon(-q)\varepsilon(p)} = 1$ because
$p \equiv 1 \pmod 4$. So $f$ is isotropic at all these places. At $p$ and $q$ it is anisotropic:
$(-q, p)_p = \left(\frac{-q}{p}\right) = \left(\frac{q}{p}\right) = -1$ since
$p \equiv 1 \pmod 4$, and $(-q, p)_q = \left(\frac{p}{q}\right) = \left(\frac{q}{p}\right) = -1$ by
quadratic reciprocity. By the local criterion for ternary forms, $f$ represents $M$ over
$\mathbb{Q}_\ell$ for $\ell \in \{p, q\}$ exactly when $M \notin pq \, (\mathbb{Q}_\ell^\times)^2$,
and the description of the squares of $\mathbb{Q}_\ell$ with
$\left(\frac{q}{p}\right) = \left(\frac{p}{q}\right) = -1$ turns these two conditions into the two
forms above.

## Sources

- J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
  98–114, <https://doi.org/10.2307/2266510>: Lemma 2, p. 108, with the remark on p. 107 that Lemmas
  1 and 2 are special cases of a general theorem of Hasse; the convention on capital and small
  letters, p. 106.
- H. Hasse, "Über die Darstellbarkeit von Zahlen durch quadratische Formen im Körper der rationalen
  Zahlen", *J. Reine Angew. Math.* 152 (1923), 129–148, as cited by J. Robinson (reference [5], p. 114):
  the general theorem of which, by Robinson, p. 107, Lemmas 1 and 2 are special cases.
- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973: Chapter I, §3.3 (the
  quadratic reciprocity law); Chapter II, §3 (the multiplicative group of $\mathbb{Q}_p$), pp. 15–19;
  Chapter III, §1 (local properties of the Hilbert symbol), pp. 19–23; Chapter IV, §2 (quadratic
  forms over $\mathbb{Q}_p$), pp. 35–41, and §3.2 (the Hasse–Minkowski theorem).
