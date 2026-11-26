# Robinson's Lemma 3: when $2 + pM^2 + pZ^2 = X^2 + Y^2$ is solvable

Let $p$ be a prime with $p \equiv 3 \pmod 4$ and let $M$ be a rational number. Then
$2 + pM^2 + pZ^2 = X^2 + Y^2$ has a solution in rational numbers $X, Y, Z$ if and only if the
denominator of $M$ in lowest terms is odd and not divisible by $p$.

This is the instance $A = 1$, $B = p$ of Robinson's formula
$2 + ABM^2 + BZ^2 = X^2 + AY^2$.

Robinson's proof: write $M = n/d$ in lowest terms and put $m = 2d^2 + pn^2$, a positive integer.
Multiplying by $d^2$ shows that the equation is solvable exactly when $m$ is represented rationally
by $X^2 + Y^2 - pZ^2$, which [Lemma 1](robinson-lemma-1.md) decides. If $d$ is odd and prime to $p$,
then $m$ is prime to $p$, so not of the form $p \cdot k \cdot S^2$, and $m \equiv 1, 2 \pmod 4$, so
not of the form $k \cdot S^2$ with $k \equiv p \equiv 3 \pmod 4$; hence $m$ is represented. If
$d = pr$, then $m = p \cdot k$ with $k = 2pr^2 + n^2$ prime to $p$ and
$\left(\frac{k}{p}\right) = \left(\frac{n^2}{p}\right) = 1$, so $m$ is not represented. If $d = 2s$,
then $n$ is odd, $m = 8s^2 + pn^2 \equiv p \pmod 8$, and $m$ is not represented.

## Depends on

- [Prime number](../../../NumberTheory/primes-primality/prime-number.md), for the prime $p$

## Proof depends on

- [Robinson's Lemma 1](robinson-lemma-1.md), for the rational values of $X^2 + Y^2 - pZ^2$
- [Legendre symbol](../../../NumberTheory/congruences/power-residues-reciprocity/legendre-symbol-and-euler-s-criterion/legendre-symbol.md), for $\left(\frac{n^2}{p}\right) = 1$ when $p \nmid n$

## Sources

- J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
  98–114, <https://doi.org/10.2307/2266510>: Lemma 3 and its proof, p. 108.
