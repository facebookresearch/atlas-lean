# Robinson's Lemma 4: when $2 + pqM^2 + pZ^2 = X^2 + qY^2$ is solvable

Let $p$ and $q$ be odd primes with $p \equiv 1 \pmod 4$ and $\left(\frac{q}{p}\right) = -1$, and
let $M$ be a rational number. Then $2 + pqM^2 + pZ^2 = X^2 + qY^2$ has a solution in rational
numbers $X, Y, Z$ if and only if the denominator of $M$ in lowest terms is divisible by neither $p$
nor $q$.

This is the instance $A = q$, $B = p$ of Robinson's formula
$2 + ABM^2 + BZ^2 = X^2 + AY^2$.

Robinson's proof: write $M = n/d$ in lowest terms and put $m = 2d^2 + pqn^2$, a positive integer.
Multiplying by $d^2$ shows that the equation is solvable exactly when $m$ is represented rationally
by $X^2 + qY^2 - pZ^2$, which [Lemma 2](robinson-lemma-2.md) decides. If $d$ is prime to $p$ and
$q$, so is $m$, and $m$ is represented. If $d = pr$, then $m = p \cdot k$ with $k = 2pr^2 + qn^2$ and
$\left(\frac{k}{p}\right) = \left(\frac{qn^2}{p}\right) = \left(\frac{q}{p}\right) = -1$, so $m$ is
not represented. If $d = qs$, then $m = q \cdot k$ with $k = 2qs^2 + pn^2$ and
$\left(\frac{k}{q}\right) = \left(\frac{pn^2}{q}\right) = \left(\frac{p}{q}\right) = \left(\frac{q}{p}\right) = -1$
by quadratic reciprocity, so $m$ is not represented.

## Depends on

- [Legendre symbol](../../../NumberTheory/congruences/power-residues-reciprocity/legendre-symbol-and-euler-s-criterion/legendre-symbol.md), for the hypothesis $\left(\frac{q}{p}\right) = -1$
- [Prime number](../../../NumberTheory/primes-primality/prime-number.md), for the primes $p$ and $q$

## Proof depends on

- [Robinson's Lemma 2](robinson-lemma-2.md), for the rational values of $X^2 + qY^2 - pZ^2$
- [Quadratic reciprocity for a prime congruent to 1 modulo 4](../../../NumberTheory/congruences/power-residues-reciprocity/quadratic-reciprocity-one-mod-four.md), for $\left(\frac{p}{q}\right) = \left(\frac{q}{p}\right)$

## Sources

- J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
  98–114, <https://doi.org/10.2307/2266510>: Lemma 4 and its proof, p. 108. In the case $q \mid d$
  the printed text writes $k = 2qr^2 + pn^2$ for $k = 2qs^2 + pn^2$, with $d = qs$.
