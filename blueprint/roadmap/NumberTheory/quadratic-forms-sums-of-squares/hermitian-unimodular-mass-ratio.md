# Mass ratio of the standard unimodular Hermitian lattices in consecutive ranks

Let $K$ be a totally real number field of degree $n$, with discriminant of absolute value $d_K$, and
let $E/K$ be a totally imaginary quadratic extension, unramified at every prime ideal of $K$. Let
$\mathcal{O}$ be the ring of integers of $E$ and $\chi$ the nontrivial character of
$\mathrm{Gal}(E/K)$, viewed on prime ideals of $K$: $\chi(\mathfrak{p}) = 1$ if $\mathfrak{p}$ splits in
$E$ and $\chi(\mathfrak{p}) = -1$ if it is inert. For $m \ge 1$ let $I_m$ be the lattice
$\mathcal{O}^m$ in the definite [Hermitian space](hermitian-local-global-principle.md) $E^m$ with
$\Phi(x, y) = \sum_{i=1}^m x_i \bar{y}_i$, that is, any lattice with an orthonormal basis. The mass of a
lattice $L$ is

$$\mathrm{Mass}(L) = \sum_{i=1}^{h} \frac{1}{\# \mathrm{Aut}(L_i)},$$

where $L_1, \dots, L_h$ represent the isometry classes of lattices in the genus of $L$ and
$\mathrm{Aut}(L_i)$ is the finite group of isometries of $L_i$. Then for every $M \ge 2$

$$\frac{\mathrm{Mass}(I_M)}{\mathrm{Mass}(I_{M-1})} = \left( \frac{(M-1)!}{(2\pi)^M} \right)^{n} d_K^{\,M - 1/2} \, L_K(\chi^M, M), \qquad L_K(\chi^M, M) = \prod_{\mathfrak{p}} \bigl(1 - \chi(\mathfrak{p})^M N\mathfrak{p}^{-M}\bigr)^{-1},$$

the product running over the prime ideals of $K$; so $L_K(\chi^M, M)$ is $\zeta_K(M)$ for even $M$ and
the $L$-function of $\chi$ at $M$ for odd $M$.

The ratio is a consequence of Siegel's mass formula in the form given by Kirschmer for Hermitian
lattices over a quadratic extension:

$$\mathrm{Mass}(L) = 2 \gamma_m^{-n} \, d_K^{\,m^2/2} \, N_{K/\mathbb{Q}}(\mathfrak{d}_{E/K})^{m(m - (-1)^m)/4} \prod_{i=1}^m L_K(\chi^i, i) \prod_{\mathfrak{p}} \lambda(L_{\mathfrak{p}}), \qquad \gamma_m = \prod_{i=1}^m \frac{(2\pi)^i}{(i-1)!},$$

for a lattice $L$ of rank $m$, where $\mathfrak{d}_{E/K}$ is the relative discriminant and the local
factors $\lambda(L_{\mathfrak{p}})$ equal $1$ for all but finitely many $\mathfrak{p}$. Here
$\mathfrak{d}_{E/K} = \mathfrak{o}_K$ because $E/K$ is unramified at every prime, every prime ideal is
good in Kirschmer's sense, and for the unimodular lattices $I_m$ Kirschmer's table of local factors gives
$\lambda(L_{\mathfrak{p}}) = 1$ at split and at inert primes. Dividing the formula for $m = M$ by the
formula for $m = M - 1$ gives the ratio. (The division is carried out here; Kirschmer states the mass
formula.)

This node is still to be broken down. A good expansion has a page for Siegel's mass formula for
Hermitian lattices over a quadratic extension in Kirschmer's form, pages for the local factors
$\lambda(L_{\mathfrak{p}})$ of the unimodular lattices $I_m$ at split and at inert primes, and the ratio
above as their consequence.

## Sources

- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>,
  Chapter 4: Definition 4.2.1 (mass), Theorem 4.2.3 (Siegel's mass formula, credited to Siegel in the
  quadratic case and to Gan and Yu in general), Proposition 4.2.7(3), Lemma 4.2.9 (local factors at good
  primes), and the definition of the $L$-series $\mathfrak{L}_K(\chi, s)$ before Corollary 4.1.5;
  Definition 3.5.1 (good prime ideals).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this ratio for $M \ge 3$, as `Formalism.HermitianLatticesTheory.SiegelMassRatio`,
  proved as `GlobalTheory.Mass.siegelMassRatio_holds`.
