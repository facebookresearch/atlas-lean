# Integrated Poincaré–Lelong formula

Let $X$ be a compact complex manifold of dimension $n$, $\bar L$ a holomorphic line bundle on $X$ with a
smooth hermitian metric $\lVert \cdot \rVert$ and first Chern form $c_1(\bar L)$, and $s$ a meromorphic
section of $L$ not identically zero on any connected component of $X$, with divisor
$\operatorname{div}(s) = \sum_j m_j Z_j$. Let $\varphi$ be a smooth real function and $\omega$ a smooth
closed real form of type $(n - 1, n - 1)$ on $X$. With $d^c = \frac{i}{4\pi}(\bar\partial - \partial)$,

$$\int_X \log \lVert s \rVert^2 \, dd^c \varphi \wedge \omega = \sum_j m_j \int_{Z_j} \varphi \, \omega
- \int_X \varphi \, c_1(\bar L) \wedge \omega,$$

where $\int_{Z_j}$ is the integral over the regular locus of $Z_j$; the integrand on the left is
integrable because $\log \lVert s \rVert^2$ is locally integrable.

This is the [Poincaré–Lelong formula](poincare-lelong-formula.md)
$dd^c [\log \lVert s \rVert^2] = \delta_{\operatorname{div}(s)} - c_1(\bar L)$, an identity of currents,
evaluated on the smooth form $\varphi \omega$, which has compact support because $X$ is compact. The
derivative of a current is defined by duality, $\langle d T, u \rangle = (-1)^{q+1} \langle T, du
\rangle$ for a current $T$ of degree $q$, and similarly for $d^c$, so that $\langle dd^c T, u \rangle =
\langle T, dd^c u \rangle$, and $dd^c(\varphi \omega) = dd^c \varphi \wedge \omega$ because the
closed form $\omega$ of pure type satisfies $\partial \omega = \bar\partial \omega = 0$. Applied on the
complex points of an arithmetic variety with smooth generic fibre to
$\omega = c_1(\bar L_1) \wedge \dots \wedge c_1(\bar L_{n-1})$ and to $\varphi = -\log \lVert 1 \rVert^2$
for a metric on the trivial line bundle, it gives the integral identities behind the independence of
arithmetic intersection numbers from the choice of sections; only the components of
$\operatorname{div}(s)$ that meet the generic fibre contribute.

## Depends on

- [Poincaré–Lelong formula](poincare-lelong-formula.md), for divisors of meromorphic sections and
  currents of integration
- [Currents of integration and the support theorems](currents-of-integration.md), for the integrals
  over the regular loci of the $Z_j$

## Proof depends on

- [Poincaré–Lelong formula](poincare-lelong-formula.md)
- [Currents of integration and the support theorems](currents-of-integration.md), for the
  derivatives of currents, defined by duality

## Sources

- J.-P. Demailly, *Complex Analytic and Differential Geometry*, version of 21 June 2012,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf>: Chapter I, (2.6)
  (derivatives of currents by duality); Chapter III, (2.15) (Lelong–Poincaré equation), pp. 143–144,
  and (3.1) (integration by parts), p. 144.
- H. Gillet and C. Soulé, "Arithmetic intersection theory", Publ. Math. IHÉS 72 (1990), 93–174,
  <http://www.numdam.org/item?id=PMIHES_1990__72__93_0>: 1.1.6 (ii) (normalization of $d^c$), p. 100,
  and (1.3.1.1), p. 103.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses a related identity, on the complex points of its arithmetic
  varieties, with smooth conjugation-invariant metrics and a sum over the horizontal components of the
  divisor, as `GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv`.
