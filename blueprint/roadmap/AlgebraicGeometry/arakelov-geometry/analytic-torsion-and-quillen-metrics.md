# Analytic torsion and Quillen metrics

Let $f \colon X \to Y$ be a projective morphism of
[arithmetic varieties](arithmetic-variety.md) over an arithmetic ring $A$ whose restriction to the
generic fibres is smooth, and choose on the relative tangent bundle $Tf_\mathbb{C}$ a hermitian metric
whose restriction to every fibre $X_y = f^{-1}(y)$, $y \in Y(\mathbb{C})$, is Kähler. Let
$\bar{\mathcal{F}}$ be a hermitian coherent sheaf on $X$ such that $Rf_* \mathcal{F}$ is a perfect
complex. The determinant of cohomology $\lambda(\mathcal{F}) = \det Rf_*(\mathcal{F})$ of Knudsen
and Mumford is a line bundle on $Y$ whose fibre at $y \in Y(\mathbb{C})$ is canonically
$\bigotimes_{q \ge 0} \det H^q(X_y, \mathcal{F}_\mathbb{C})^{(-1)^q}$. On this fibre, Hodge theory
identifies $H^q(X_y, \mathcal{F}_\mathbb{C})$ with the kernel of the Laplacian
$\Delta_q = \bar\partial \bar\partial^* + \bar\partial^* \bar\partial$ on forms of type $(0, q)$,
which gives an $L^2$ metric $h_{L^2}$; the zeta function
$\zeta_q(s) = \operatorname{Tr}(\Delta_q^{-s} \mid (\ker \Delta_q)^\perp)$ converges for
$\operatorname{Re} s > \dim X_y$, continues meromorphically to $\mathbb{C}$ and is regular at $0$;
the Ray–Singer analytic torsion is $T(X_y, \mathcal{F}) = \sum_{q \ge 0} (-1)^{q+1} q \,
\zeta_q'(0)$; and the Quillen metric is $h_Q = h_{L^2} \exp(T(X_y, \mathcal{F}))$. Bismut, Gillet and
Soulé proved that $h_Q$ is a smooth metric on the line bundle $\lambda(\mathcal{F})_\mathbb{C}$, so
that $(\lambda(\mathcal{F}), h_Q)$ is a hermitian line bundle on $Y$.

This node is still to be broken down: the definitions above are precise, but the analytic theorems
on which the [arithmetic Riemann–Roch theorem](arithmetic-riemann-roch-theorem.md) and Gillet and
Soulé's form of the [arithmetic Hilbert–Samuel theorem](arithmetic-hilbert-samuel-theorem.md) rest
are not. A good expansion has pages for:

- the zeta-regularized determinant of the Laplacian and the Ray–Singer analytic torsion of a
  hermitian holomorphic vector bundle on a compact Kähler manifold (Ray–Singer; Gillet–Soulé,
  4.1.1);
- the Quillen metric on the determinant of cohomology and its smoothness in families (Bismut, Gillet
  and Soulé, "Analytic torsion and holomorphic determinant bundles", Corollary 3.9, as cited in
  4.1.2);
- the immersion formula of Bismut and Lebeau, which computes, for a closed immersion
  $i \colon X \to P$ and a resolution $0 \to E_m \to \dots \to E_0 \to i_* E \to 0$ by hermitian
  vector bundles, the difference $\hat c_1(\lambda(E), h_Q) - \sum_{j \ge 0} (-1)^j \hat c_1(\lambda(E_j),
  h_Q)$, and the matching computation of Bismut, Gillet and Soulé ("Complex immersions and Arakelov
  geometry", Theorem 4.13);
- Gillet and Soulé's computation of the analytic torsion of the trivial bundle on projective spaces,
  which proves the arithmetic Riemann–Roch formula for the trivial bundle on $\mathbb{P}^N$ over
  $\operatorname{Spec} \mathbb{Z}$ ("Analytic torsion and the arithmetic Todd genus", Theorem 1);
- the asymptotics of Bismut and Vasserot of the analytic torsion $T(X, \mathcal{F} \otimes L^{\otimes
  n})$ for a positive hermitian line bundle $L$ as $n \to \infty$ (Bismut–Vasserot, Theorem 8, as used
  in the proof of Gillet and Soulé's Theorem 8).

## Depends on

- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md)

## Sources

- H. Gillet and C. Soulé, "An arithmetic Riemann–Roch theorem", Invent. Math. 110 (1992), 473–543,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0110>: introduction, pp. 473–474 (the Quillen
  metric, the proof through Bismut–Lebeau, Bismut–Gillet–Soulé Theorem 4.13 and the arithmetic Todd
  genus); 4.1.1 (Ray–Singer analytic torsion and the Quillen metric, pp. 522–523) and 4.1.2 (the
  determinant of cohomology of a hermitian coherent sheaf and the smoothness of $h_Q$, p. 523);
  5.1.3 with formula (42) (the asymptotics of Bismut and Vasserot in the proof of Theorem 8,
  pp. 535–536).
- J.-M. Bismut, H. Gillet and C. Soulé, "Analytic torsion and holomorphic determinant bundles I, II,
  III", Comm. Math. Phys. 115 (1988), 49–78, 79–126 and 301–351: Corollary 3.9, as cited by Gillet
  and Soulé.
- J.-M. Bismut, H. Gillet and C. Soulé, "Complex immersions and Arakelov geometry", in *The
  Grothendieck Festschrift I*, Birkhäuser, 1990, 249–331: Theorem 4.13, as cited by Gillet and Soulé.
- J.-M. Bismut and G. Lebeau, "Complex immersions and Quillen metrics", Publ. Math. IHÉS 74 (1991).
- H. Gillet and C. Soulé, "Analytic torsion and the arithmetic Todd genus", with an appendix by
  D. Zagier, Topology 30 (1991), 21–54: Theorem 1, as cited by Gillet and Soulé.
- J.-M. Bismut and E. Vasserot, "The asymptotics of the Ray–Singer analytic torsion associated with
  high powers of a positive line bundle", Comm. Math. Phys. 125 (1989), 355–367: Theorem 8.
- D. B. Ray and I. M. Singer, "Analytic torsion for complex manifolds", Ann. of Math. (2) 98 (1973),
  154–177.
- F. Knudsen and D. Mumford, "The projectivity of the moduli space of stable curves I: preliminaries
  on 'det' and 'Div'", Math. Scand. 39 (1976), 19–55.
