# Dedekind zeta function of a quadratic field as $\zeta(s) L(s, \chi_D)$

Let $K$ be a quadratic field of discriminant $D$, let $\zeta_K(s) = \sum_{\mathfrak{a}} N(\mathfrak{a})^{-s}$ be its
Dedekind zeta function, the sum running over the nonzero ideals $\mathfrak{a}$ of the ring of integers
$\mathcal{O}_K$ and $N(\mathfrak{a}) = \#(\mathcal{O}_K / \mathfrak{a})$ being the [absolute norm](../../../RingTheory/dedekind-domains/ideal-absolute-norm.md), and let $\chi_D(n) = \left(\frac{D}{n}\right)$ be the Kronecker symbol, a Dirichlet character
modulo $|D|$. Then

$$\zeta_K(s) = \zeta(s) \, L(s, \chi_D) \qquad (\operatorname{Re} s > 1),$$

where $\zeta$ is the Riemann zeta function and $L(s, \chi_D) = \sum_{n \ge 1} \chi_D(n) n^{-s}$.

Both sides are absolutely convergent Euler products for $\operatorname{Re} s > 1$. By
[unique factorisation](../../../RingTheory/dedekind-domains/ideal-unique-factorization.md), every nonzero ideal of $\mathcal{O}_K$ is uniquely a product of irreducible ideals,
which are its nonzero prime ideals because an ideal of a Dedekind domain
[divides exactly the ideals it contains](../../../RingTheory/dedekind-domains/characterizations-of-dedekind-domains/is-dedekind-domain-iff-contain-is-divide.md); with the multiplicativity of $N$ and the absolute
convergence of $\sum_{\mathfrak{p}} N\mathfrak{p}^{-\sigma}$ for $\sigma > 1$, this makes $\zeta_K(s)$ the product over the
nonzero prime ideals $\mathfrak{p}$ of $\mathcal{O}_K$ of $(1 - N\mathfrak{p}^{-s})^{-1}$. In the same way, since the nonzero
ideals $n\mathbb{Z}$ of the Dedekind domain $\mathbb{Z}$ factor uniquely into the prime ideals $p\mathbb{Z}$ and $\chi_D$ is
completely multiplicative, $L(s, \chi_D)$ is the product over the primes $p$ of $(1 - \chi_D(p) p^{-s})^{-1}$, the series
$\sum_n |\chi_D(n) n^{-s}|$ being dominated by $\zeta(\sigma)$. The identity then holds prime
by prime: by the [decomposition of rational primes in $K$](../../algebraic-number-theory/quadratic-fields/quadratic-field-prime-decomposition.md),
the factor of $\zeta_K$ at the prime ideals above a prime number $p$ is $(1 - p^{-s})^{-2}$ if
$\chi_D(p) = 1$, $(1 - p^{-2s})^{-1}$ if $\chi_D(p) = -1$ and $(1 - p^{-s})^{-1}$ if $\chi_D(p) = 0$, which is
$(1 - p^{-s})^{-1} (1 - \chi_D(p) p^{-s})^{-1}$ in each case.

## Depends on

- [Quadratic Dirichlet character of a fundamental discriminant](../../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/quadratic-dirichlet-character.md)
- [Absolute norm of an ideal](../../../RingTheory/dedekind-domains/ideal-absolute-norm.md), for $N$

## Proof depends on

- [Decomposition of rational primes in a quadratic field](../../algebraic-number-theory/quadratic-fields/quadratic-field-prime-decomposition.md)
- [Summability of Dedekind zeta terms for σ > 1](dedekind-zeta-function-and-polar-density/summable-height-one-spectrum-abs-norm-rp.md), for the absolute convergence of the Euler product of $\zeta_K$
- [Unique factorisation of ideals in a Dedekind domain](../../../RingTheory/dedekind-domains/ideal-unique-factorization.md), for the Euler products of $\zeta_K(s)$ and $L(s, \chi_D)$
- [Absolute norm of an ideal](../../../RingTheory/dedekind-domains/ideal-absolute-norm.md), for $N(IJ) = N(I) N(J)$, in the Euler product of $\zeta_K(s)$
- [Dedekind domains as the Noetherian domains where to contain is to divide](../../../RingTheory/dedekind-domains/characterizations-of-dedekind-domains/is-dedekind-domain-iff-contain-is-divide.md), for the irreducible ideals being the nonzero prime ideals

## Sources

- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf> (copy:
  <https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf>), Chapter 2, §1,
  p. 67: "the trivial decomposition $\zeta_d(s) = \zeta(s) L_d(s)$", with $L_d(s) = \sum_n \left(\frac{d}{n}\right) n^{-s}$.
- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>,
  Section 4.1: Theorem 4.1.2 (Euler product of $\zeta_F$) and equation (4.1.1), $L_K(\chi, s) = \zeta_F(s) / \zeta_K(s)$
  for $\operatorname{Re} s > 1$, for a quadratic extension $F$ of a totally real field $K$ and the nontrivial character
  $\chi$ of $\mathrm{Gal}(F/K)$, with the associated function on prime ideals of $K$ equal to $0$, $-1$, $1$ at the
  primes that ramify, are inert and split in $F$; here $K = \mathbb{Q}$.
- D. Zagier, *Elliptic modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  Universitext, Springer (2008), 1–103,
  <https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1007/978-3-540-74119-0_1/fulltext.pdf>, §6.3, p. 84:
  the multiplicative decomposition $\zeta_K(s) = \zeta(s) L(s, \chi_D)$.
