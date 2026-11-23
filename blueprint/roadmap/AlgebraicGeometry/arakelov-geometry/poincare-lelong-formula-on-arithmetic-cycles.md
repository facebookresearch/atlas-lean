# Poincaré–Lelong formula on arithmetic cycles

This node is still to be broken down. It covers the integrated Poincaré–Lelong formula on the
complex points of an integral horizontal cycle of an [arithmetic variety](arithmetic-variety.md)
whose generic fibre may be singular, in the form that Alpöge's library uses. No published source
stating it in this form has been identified: it is recorded here as an unsourced target, not as a
consequence of the
[integrated Poincaré–Lelong formula](../birational-geometry/integrated-poincare-lelong-formula.md)
on a compact complex manifold.

The target, in the library's form, is the following. Let $X$ be an integral closed subscheme of a
product of projective spaces over $\mathbb{Z}$, flat over $\mathbb{Z}$, given by a multihomogeneous
prime ideal $P$, of dimension $n + 2$, so that $X(\mathbb{C})$ has complex dimension $n + 1$; no
smoothness of the generic fibre is assumed (for example $X$ may be the plane cuspidal cubic $y^2 z =
x^3$ over $\mathbb{Z}$, with $n = 0$). Let $\bar L_1, \dots, \bar L_n$, $\bar A$ and $\bar B$ be
line bundles on the ambient product with smooth metrics invariant under complex conjugation, $\bar
B$ having multidegree $0$, so that it is the trivial bundle with a metric $h_B$ and $\log h_B$ is a
smooth function, and let $s$ be a multihomogeneous section of $A$ not vanishing identically on $X$.
Then
$$\int_{X(\mathbb{C})} \log \frac{|s|}{h_A} \; dd^c \log h_B \wedge \omega_{\bar L} \;=\; \sum_W m_W(s)
\int_{W(\mathbb{C})} \log h_B \; \omega_{\bar L} \;-\; \int_{X(\mathbb{C})} \log h_B \; dd^c \log h_A
\wedge \omega_{\bar L},$$
where $\omega_{\bar L} = dd^c \log h_{L_1} \wedge \dots \wedge dd^c \log h_{L_n}$ is formed from the
potentials $\log h_{L_j}$ of the metrics, with the library's normalization of $dd^c$; the sum runs
over the **horizontal** components $W$ of the divisor of $s$ on $X$, that is, over the minimal
primes of $P + (s)$ that are flat over $\mathbb{Z}$, and $m_W(s)$ is the length of the local ring of
$X / (s)$ at $W$; vertical components do not contribute. The integrand on the left is the logarithm
of the norm of $s$, not of its square, and the integrals over the possibly singular $X(\mathbb{C})$
and $W(\mathbb{C})$ are defined by integrating, over the target of a linear projection that is
finite on $X(\mathbb{C})$, the sum over the sheets of a density built from these potentials (and as
$0$ when no such projection exists).

A good expansion has pages for: the comparison of these sheet integrals with integration over the
regular loci of $X(\mathbb{C})$ and $W(\mathbb{C})$, and the local integrability of $\log |s|$
against the mixed curvature forms; a resolution of singularities $\tilde X \to X_\mathbb{Q}$, on
which the
[integrated Poincaré–Lelong formula](../birational-geometry/integrated-poincare-lelong-formula.md)
applies, and the push-forward of the divisor of $s$, with multiplicities given by algebraic lengths,
along it (Gillet–Soulé, §§3.3.2–3.3.3, pp. 126–127, treat an integral cycle in a smooth arithmetic
ambient in this way; Demailly, *Complex Analytic and Differential Geometry*, Chapter III,
(4.10)–(4.12), pp. 155–157, for intersections with currents of integration); the separation of
horizontal and vertical components; and the normalizations: the factor $2$ between $\log |s|$ and
$\log |s|^2$, and the convention for $dd^c$ (Gillet–Soulé, 1.1.6 (ii)).

## Depends on

- [Arithmetic variety](arithmetic-variety.md), for arithmetic varieties, their complex points and
  hermitian line bundles
- [Integrated Poincaré–Lelong formula](../birational-geometry/integrated-poincare-lelong-formula.md),
  for the case of a compact complex manifold

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
  `ptsIntegral` (sheet integrals over a linear projection), `logNorm` ($\log(|s|/h_A)$), `multAt`
  (local lengths) and the hypothesis `B.a = 0`.
