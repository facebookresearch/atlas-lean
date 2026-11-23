# Poincaré–Lelong formula on arithmetic cycles

This node is still to be broken down. It covers the integrated Poincaré–Lelong formula on the
complex points of an integral horizontal cycle of an [arithmetic variety](arithmetic-variety.md)
whose generic fibre may be singular, in the form that Alpöge's library uses. No published source
stating it in this form has been identified: it is recorded here as an unsourced target, not as a
consequence of the
[integrated Poincaré–Lelong formula](../birational-geometry/integrated-poincare-lelong-formula.md)
on a compact complex manifold.

The target, in the library's form, is the following. Let $X$ be an integral closed subscheme of a
product of projective spaces $\prod_k \mathbb{P}_\mathbb{Z}$, flat over $\mathbb{Z}$, given by a
multihomogeneous prime ideal $P$ of the multigraded polynomial ring that is *relevant* (in every
block some coordinate variable is not in $P$), with $X$ of dimension $n + 2$, so that
$X(\mathbb{C})$ has complex dimension $n + 1$ (the dimension is that of the multiprojective scheme
$X$; its multihomogeneous coordinate ring has dimension $n + 2$ plus the number of blocks); no
smoothness of the generic fibre is assumed (for example $X$ may be the plane cuspidal cubic $y^2 z =
x^3$ over $\mathbb{Z}$, with $n = 0$). Let $\bar L_1, \dots, \bar L_n$, $\bar A$ and $\bar B$ be
line bundles on the ambient product with smooth metrics invariant under complex conjugation, $\bar
B$ having multidegree $0$, so that it is the trivial bundle with a metric $h_B$ and $\log h_B$ is a
smooth function, and let $s$ be an integral multihomogeneous polynomial of the multidegree of $A$,
which is then nonnegative, not in $P$. Then

$$\int_{X(\mathbb{C})} \log \frac{|s|}{h_A} \; dd^c \log h_B \wedge \omega_{\bar L} \;=\; \sum_W
m_W(s) \int_{W(\mathbb{C})} \log h_B \; \omega_{\bar L} \;-\; \int_{X(\mathbb{C})} \log h_B \; dd^c
\log h_A \wedge \omega_{\bar L},$$

where $\omega_{\bar L} = dd^c \log h_{L_1} \wedge \dots \wedge dd^c \log h_{L_n}$ is formed from the
potentials $\log h_{L_j}$ of the metrics and $dd^c = (i/\pi) \partial\bar\partial$, twice the
operator $(i/2\pi) \partial\bar\partial$ of Gillet and Soulé: $dd^c \log |f| = dd^c_{\mathrm{GS}}
\log |f|^2$, so that with the logarithm of the norm, not of its square, a simple zero of a function
has coefficient $1$ in its divisor. The sum runs over the minimal primes $W$ of $P + (s)$ that are
both **relevant** and **horizontal**, $W \cap \mathbb{Z} = 0$, and $m_W(s)$ is the length of the
localization at $W$ of the quotient of the polynomial ring by $P + (s)$; vertical components do not
contribute. The relevance condition matters: on $\mathbb{P}^0_\mathbb{Z} \times
\mathbb{P}^1_\mathbb{Z}$, with $P = 0$ and $s = U$ the only coordinate of the first block, $(U)$ is
a horizontal minimal prime of $(s)$, but $U$ vanishes nowhere on the product.

The integrals over the possibly singular complex points are sheet integrals, defined separately for
each cycle. For a relevant horizontal prime $W$ whose multiprojective scheme has dimension $e + 1$,
let its *open multicone* be the set of points $z$ with a nonzero coordinate in every block at which
the polynomials of $W$ vanish. A *good projection* is a complex linear map $\Psi$ from the Segre
coordinates to $\mathbb{C}^{e+1}$ with $\Psi(\operatorname{segre} z) \ne 0$ at every point $z$ of
the open multicone; each cycle, $X$ and each $W$, has its own. The condition is not tested at the
vertex of the affine cone, nor at a point with a zero block, whose Segre image is $0$ for every
$\Psi$; on $\mathbb{P}^0_\mathbb{Z}$, for instance, the identity is a good projection on
$\mathbb{C}^\times$ and the slice has one sheet. The integral of $g\, dd^c \varphi_1 \wedge \dots
\wedge dd^c \varphi_e$ is the integral over $y \in \mathbb{C}^e$ of the sum, over the points $w$ of
the Segre image of the open multicone with $\Psi(w) = (1, y)$, of $g$ times the density of $dd^c
\varphi_1 \wedge \dots \wedge dd^c \varphi_e$ pulled back along a holomorphic local sheet through
$w$, that is, $e!\,(2/\pi)^e$ times the real part of the mixed discriminant of the complex Hessians;
a point with no such sheet contributes $0$, and the integral is $0$ when no good projection exists.
That these fibres are finite is a property to prove, not part of the definition.

A good expansion has pages for: the existence of good projections and the finiteness of their
fibres; the comparison of these sheet integrals with integration over the regular loci of
$X(\mathbb{C})$ and $W(\mathbb{C})$, and their independence of the projection; the local
integrability of $\log |s|$ against the mixed curvature forms; a resolution of singularities $\tilde
X \to X_\mathbb{Q}$, on which the
[integrated Poincaré–Lelong formula](../birational-geometry/integrated-poincare-lelong-formula.md)
applies, and the push-forward of the divisor of $s$, with multiplicities given by algebraic lengths,
along it (Gillet–Soulé, §§3.3.2–3.3.3, pp. 126–127, treat an integral cycle in a smooth arithmetic
ambient in this way; Demailly, *Complex Analytic and Differential Geometry*, Chapter III,
(4.10)–(4.12), pp. 155–157, for intersections with currents of integration); and the separation of
relevant horizontal, irrelevant and vertical components. None of these sources proves the identity
with the sheet integrals defined above.

## Depends on

- [Arithmetic variety](arithmetic-variety.md), for arithmetic varieties, their complex points and
  hermitian line bundles

## Proof depends on

- [Integrated Poincaré–Lelong formula](../birational-geometry/integrated-poincare-lelong-formula.md),
  for the case of a compact complex manifold, applied on a resolution
- [Resolution of singularities of quasi-projective varieties](../birational-geometry/resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md),
  for a resolution of the generic fibre

## Sources

- H. Gillet and C. Soulé, "Arithmetic intersection theory", Publ. Math. IHÉS 72 (1990), 93–174,
  <http://www.numdam.org/item?id=PMIHES_1990__72__93_0>: 1.1.6 (ii) (normalization of $d^c$), p.
  100; §§3.3.2–3.3.3, pp. 126–127.
- J.-P. Demailly, *Complex Analytic and Differential Geometry*, version of 21 June 2012,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf>: Chapter III,
  (4.10)–(4.12), pp. 155–157.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states the target as `GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv`, with
  `ptsIntegral` (sheet integrals over a good projection `IsGoodProj`), `maDensity` (the density
  above), `logNorm` ($\log(|s|/h_A)$), `divSupp` (relevant minimal primes), `IsHorizontal`, `multAt`
  (local lengths) and the hypothesis `B.a = 0`.
