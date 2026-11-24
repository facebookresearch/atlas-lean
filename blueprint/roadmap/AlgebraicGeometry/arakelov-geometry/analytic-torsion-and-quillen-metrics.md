# Analytic torsion and Quillen metrics

This node is still to be broken down: its definitions are precise, but the analytic theorems below
are not.

Let $f \colon X \to Y$ be a projective morphism of [arithmetic varieties](arithmetic-variety.md),
quasi-projective over an arithmetic ring $A$ as in Gillet and Soulé's Inventiones paper, whose
restriction to the generic fibres is smooth, and choose on the relative tangent bundle
$Tf_\mathbb{C}$ a smooth hermitian metric $h_X$, invariant under complex conjugation, whose
restriction to every fibre $X_y = f^{-1}(y)$, $y \in Y(\mathbb{C})$, is Kähler. Let
$\bar{\mathcal{F}}$ be a hermitian coherent sheaf on $X$, locally free on the generic fibre with a
smooth metric invariant under conjugation on the resulting vector bundle $\mathcal{F}_\mathbb{C}$,
such that $Rf_* \mathcal{F}$ is a perfect complex. The determinant of cohomology
$\lambda(\mathcal{F}) = \det Rf_*(\mathcal{F})$ of Knudsen and Mumford is a line bundle on $Y$ whose
fibre at $y \in Y(\mathbb{C})$ is canonically $\bigotimes_{q \ge 0} \det H^q(X_y,
\mathcal{F}_\mathbb{C})^{(-1)^q}$. On a fibre $X_y$ of complex dimension $d$, let $\omega_0 =
\frac{i}{2\pi} \sum_{\alpha, \beta} h_X(\partial/\partial z_\alpha, \partial/\partial z_\beta) \,
dz_\alpha \wedge d\bar z_\beta$ and give the spaces of $\mathcal{F}_\mathbb{C}|_{X_y}$-valued forms
of type $(0, q)$ the scalar product $\langle s, t \rangle = \int_{X_y} \langle s(x), t(x) \rangle \,
\omega_0^d / d!$. Hodge theory identifies $H^q(X_y, \mathcal{F}_\mathbb{C})$ with the kernel of the
Laplacian $\Delta_q = \bar\partial \bar\partial^* + \bar\partial^* \bar\partial$, which induces the
$L^2$ scalar product $h_{L^2}$ on $\lambda(\mathcal{F})_y$; the zeta function $\zeta_q(s) =
\operatorname{Tr}(\Delta_q^{-s} \mid (\ker \Delta_q)^\perp)$ converges for $\operatorname{Re} s >
d$, continues meromorphically to $\mathbb{C}$ and is regular at $0$; the Ray–Singer analytic torsion
is $T(X_y, \mathcal{F}) = \sum_{q \ge 0} (-1)^{q+1} q \, \zeta_q'(0)$; and the Quillen metric is the
hermitian scalar product $h_Q = h_{L^2} \exp(T(X_y, \mathcal{F}))$, whose norm is $\lVert \cdot
\rVert_Q = \lVert \cdot \rVert_{L^2} \exp(T(X_y, \mathcal{F})/2)$. Bismut, Gillet and Soulé proved
that the Quillen metric is smooth (on the inverse of the Knudsen–Mumford determinant, in their
convention, with norms instead of scalar products and the Laplacian $2\Delta$), so that
$(\lambda(\mathcal{F}), h_Q)$ is a hermitian line bundle on $Y$.

The definitions above are precise, but the analytic theorems on which the
[arithmetic Riemann–Roch theorem](arithmetic-riemann-roch-theorem.md) and Gillet and Soulé's form of
the [arithmetic Hilbert–Samuel theorem](arithmetic-hilbert-samuel-theorem.md) rest are not. A good
expansion has pages for:

- the zeta-regularized determinant $\det' \Delta_q = \exp(-\zeta_q'(0))$ and the analytic torsion of
  a hermitian holomorphic vector bundle on a compact Kähler manifold (Ray and Singer, for flat
  bundles; Gillet–Soulé, Invent. 4.1.1, and Topology §§1.1.1–1.1.3, where the analogous sum has the
  opposite sign);
- the Quillen metric on the determinant of cohomology, its smoothness in families (Bismut, Gillet
  and Soulé, "Analytic torsion and holomorphic determinant bundles III", Corollary 3.9), the
  curvature theorem for it (I, Theorem 0.1; III, p. 350) and the anomaly formulas for a change of
  the metrics (I, Theorems 0.2–0.3; Gillet–Soulé, Topology, Theorem 1.4 (i));
- the immersion formula: for $f = g \circ i$ with a closed immersion $i \colon X \to P$ over the
  common base $Y$, a Kähler metric on $P$ and a resolution $0 \to E_m \to \dots \to E_0 \to i_* E
  \to 0$ by hermitian vector bundles satisfying Bismut's condition (A) for the induced metrics on
  $X$ and on the normal bundle, Bismut and Lebeau compute the logarithm of the squared Quillen norm
  of the canonical isomorphism $\lambda_f(E) \cong \bigotimes_j \lambda_g(E_j)^{(-1)^j}$ (Theorem
  0.1, (0.5)), and, separately, Bismut, Gillet and Soulé's Theorem 4.13 proves the corresponding
  pushed-forward identity of arithmetic classes on the base for smooth projective morphisms of
  regular arithmetic varieties, which Gillet and Soulé extend to projective local complete
  intersection morphisms smooth on the generic fibre (Invent. 4.2.3); for the coherent form of the
  arithmetic Riemann–Roch theorem they use instead Lemma 21 and 4.2.2 of the Inventiones paper;
- Gillet and Soulé's computation of the analytic torsion of the trivial bundle on projective spaces
  with the Fubini–Study metric, which proves the arithmetic Riemann–Roch formula for the trivial
  bundle on $\mathbb{P}^N_\mathbb{Z}$ (Topology, Theorem 2.1.1 and Remarks 2.1.2);
- the asymptotics of Bismut and Vasserot of the analytic torsion of $F \otimes L^{\otimes n}$, for a
  holomorphic hermitian vector bundle $F$ on a compact complex manifold (in the application,
  $\mathcal{F}_\mathbb{C}$ or its pull-back) and a positive hermitian line bundle $L$, as $n \to
  \infty$ (Theorem 8) and the variation of the $L^2$ metrics (Theorem 10), used in the proof of
  Gillet and Soulé's Theorem 8.

## Depends on

- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md)

## Proof depends on

- [Arithmetic characteristic classes of hermitian vector bundles](arithmetic-chern-classes.md), for
  the secondary Bott–Chern classes in the anomaly formulas

## Sources

- H. Gillet and C. Soulé, "An arithmetic Riemann–Roch theorem", Invent. Math. 110 (1992), 473–543,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0110>: introduction, pp. 473–474; Definition 4,
  p. 495 (condition (A)); 4.1.1 (formula (10): the Kähler form, the Laplacian, analytic torsion and
  the Quillen metric, pp. 522–523) and 4.1.2 (the determinant of cohomology of a hermitian coherent
  sheaf and the smoothness of $h_Q$, p. 523); Lemma 21, p. 512; 4.2.1–4.2.3 (the immersion step, pp.
  528–532, with 4.2.2, pp. 528–531, and (31)–(33), pp. 531–532); 5.1.3 with formulas (37), (42),
  (44)–(46) (the theorems of Bismut and Vasserot in the proof of Theorem 8, pp. 535–538).
- J.-M. Bismut, H. Gillet and C. Soulé, "Analytic torsion and holomorphic determinant bundles I, II,
  III", Comm. Math. Phys. 115 (1988), 49–78, 79–126 and 301–351: I, (0.1), p. 50 (the inverse of the
  Knudsen–Mumford determinant), Theorems 0.1–0.3, pp. 50–51 (curvature and anomaly); III, p. 350;
  III, Definitions 1.4–1.5 and Theorem 1.6, pp. 308–309, and Corollary 3.9, p. 346 (smoothness of
  the Quillen metric).
- J.-M. Bismut, H. Gillet and C. Soulé, "Complex immersions and Arakelov geometry", in *The
  Grothendieck Festschrift I*, Birkhäuser, 1990, 249–331: §4 (f), Theorem 4.13, pp. 327–329.
- J.-M. Bismut and G. Lebeau, "Complex immersions and Quillen metrics", Publ. Math. IHÉS 74 (1991),
  1–298: Theorem 0.1 and (0.5), pp. 1–3; §I (e), Definition 1.10 and Remark 1.11, pp. 23–24 (its
  normalizations of the volume and of the Laplacian).
- H. Gillet and C. Soulé, "Analytic torsion and the arithmetic Todd genus", with an appendix by D.
  Zagier, Topology 30 (1991), 21–54: §§1.1.1–1.1.3, pp. 22–24; Conjecture 1.3, pp. 25–26; Theorem
  1.4 (i), p. 26; Theorem 2.1.1 and Remarks 2.1.2, p. 29.
- J.-M. Bismut and E. Vasserot, "The asymptotics of the Ray–Singer analytic torsion associated with
  high powers of a positive line bundle", Comm. Math. Phys. 125 (1989), 355–367: Definition 6,
  Remark 7 and Theorem 8, (38), pp. 362–363; Theorem 10, (55), p. 365.
- D. B. Ray and I. M. Singer, "Analytic torsion for complex manifolds", Ann. of Math. (2) 98 (1973),
  154–177 (flat holomorphic bundles).
- F. Knudsen and D. Mumford, "The projectivity of the moduli space of stable curves I: preliminaries
  on 'det' and 'Div'", Math. Scand. 39 (1976), 19–55: Theorem 2, pp. 41–42.
