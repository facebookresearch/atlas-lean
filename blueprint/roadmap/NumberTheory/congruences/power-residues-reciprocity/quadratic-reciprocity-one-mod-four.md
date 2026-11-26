# Quadratic reciprocity for a prime congruent to 1 modulo 4

Let $p$ and $q$ be primes with $p \equiv 1 \pmod 4$ and $q \neq 2$. Then
$\left(\frac{p}{q}\right) = \left(\frac{q}{p}\right)$, where $\left(\frac{\cdot}{\cdot}\right)$ is
the Legendre symbol. When $p = q$ both sides are $0$.

This is the case $p \equiv 1 \pmod 4$ of the law of quadratic reciprocity
$\left(\frac{q}{p}\right)\left(\frac{p}{q}\right) = (-1)^{\frac{p-1}{2}\frac{q-1}{2}}$ for distinct
odd primes $p$ and $q$.

## Sources

- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973: Chapter I,
  §3.3 (the quadratic reciprocity law).
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842:
  [legendreSym.quadratic_reciprocity_one_mod_four](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean#L133 "legendreSym.quadratic_reciprocity_one_mod_four").
