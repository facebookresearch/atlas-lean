# Mass ratio of the standard unimodular Hermitian lattices in consecutive ranks

Let $K$ be a totally real number field of degree $n$, with discriminant of absolute value $d_K$, and let $E/K$ be a
totally imaginary quadratic extension, unramified at every prime ideal of $K$. Let $\mathcal{O}$ be the ring of integers
of $E$ and $\chi$ the nontrivial character of $\mathrm{Gal}(E/K)$, viewed on prime ideals of $K$: $\chi(\mathfrak{p}) = 1$ if
$\mathfrak{p}$ splits in $E$ and $\chi(\mathfrak{p}) = -1$ if it is inert. For $m \ge 1$ let $I_m$ be the lattice $\mathcal{O}^m$ in the
definite [Hermitian space](hermitian-local-global-principle.md) $E^m$ with $\Phi(x, y) = \sum_{i=1}^m x_i \bar{y}_i$, that is,
any lattice with an orthonormal basis, and let $\mathrm{Mass}(L)$ be the
[mass](hermitian-siegel-mass-formula.md) of the genus of a lattice $L$. Then for every $M \ge 2$

$$\frac{\mathrm{Mass}(I_M)}{\mathrm{Mass}(I_{M-1})} = \left( \frac{(M-1)!}{(2\pi)^M} \right)^{n} d_K^{\,M - 1/2} \, L_K(\chi^M, M), \qquad L_K(\chi^M, M) = \prod_{\mathfrak{p}} \bigl(1 - \chi(\mathfrak{p})^M N\mathfrak{p}^{-M}\bigr)^{-1},$$

the product running over the prime ideals of $K$; so $L_K(\chi^M, M)$ is $\zeta_K(M)$ for even $M$ and the $L$-function of
$\chi$ at $M$ for odd $M$.

Proof. Since $E/K$ is unramified at every prime ideal, no prime ideal divides the relative discriminant
$\mathfrak{d}_{E/K}$, which is therefore the unit ideal, and
every prime ideal $\mathfrak{p}$ of $K$ splits or is inert in $E$. The lattice $I_m$ is integral and $(I_m)_{\mathfrak{p}}$ is
unimodular at every $\mathfrak{p}$, as $I_m$ has an orthonormal basis, so its local factor is $\lambda((I_m)_{\mathfrak{p}}) = 1$ at the
[split primes](hermitian-unimodular-local-factor-split.md) and at the
[inert primes](hermitian-unimodular-local-factor-inert.md), that is, at every $\mathfrak{p}$.
[Siegel's mass formula](hermitian-siegel-mass-formula.md) then gives

$$\mathrm{Mass}(I_m) = 2 \gamma_m^{-n} \, d_K^{\,m^2/2} \prod_{i=1}^{m} L_K(\chi^i, i), \qquad \gamma_m = \prod_{i=1}^m \frac{(2\pi)^i}{(i-1)!},$$

and dividing the formula for $m = M$ by the formula for $m = M - 1$ gives the ratio, since
$\gamma_M / \gamma_{M-1} = (2\pi)^M / (M - 1)!$ and $M^2/2 - (M - 1)^2/2 = M - 1/2$. (The division is carried out here;
Kirschmer states the mass formula.)

## Depends on

- [Siegel's mass formula for definite Hermitian lattices over a quadratic extension](hermitian-siegel-mass-formula.md), for the mass of a genus

## Proof depends on

- [Siegel's mass formula for definite Hermitian lattices over a quadratic extension](hermitian-siegel-mass-formula.md), for the formula in terms of the local factors
- [Local factor of a unimodular Hermitian lattice at a split prime](hermitian-unimodular-local-factor-split.md)
- [Local factor of a unimodular Hermitian lattice at an inert prime](hermitian-unimodular-local-factor-inert.md)
- [Unramified primes are those not dividing the discriminant](../../RingTheory/ramification/different-and-discriminant-ideals/is-unramified-in-iff-not-dvd-discriminan.md), for $\mathfrak{d}_{E/K} = (1)$

## Sources

- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>,
  Chapter 4: Definition 4.2.1 (mass), Proposition 4.2.7(3) (Siegel's mass formula in terms of the local factors
  $\lambda(L_{\mathfrak{p}})$), Lemma 4.2.9 (local factors at good primes), and the definition of the $L$-series
  $L_K(\chi, s)$ before Corollary 4.1.5.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this ratio for $M \ge 3$, as `Formalism.HermitianLatticesTheory.SiegelMassRatio`,
  proved as `GlobalTheory.Mass.siegelMassRatio_holds`.
