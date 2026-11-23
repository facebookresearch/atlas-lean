# Arithmetic Riemann–Roch theorem

Let $A$ be an arithmetic ring with fraction field $F$, and let $f \colon X \to Y$ be a projective
morphism of regular arithmetic varieties, quasi-projective over $A$, whose restriction $X_F \to Y_F$
to the generic fibres is smooth. Choose on the relative tangent bundle $Tf_\mathbb{C}$ of
$X(\mathbb{C}) \to Y(\mathbb{C})$ a smooth hermitian metric, invariant under complex conjugation,
whose restriction to every fibre $X_y = f^{-1}(y)$, $y \in Y(\mathbb{C})$, is Kähler (it need not
extend to a Kähler metric on $X(\mathbb{C})$), and let $\bar E$ be a hermitian vector bundle on $X$.
Let $\lambda(E) = \det Rf_* E$ be the determinant of cohomology, a line bundle on $Y$ whose fibre at
$y \in Y(\mathbb{C})$ is $\bigotimes_{q \ge 0} \det H^q(X_y, E)^{(-1)^q}$, and let $h_Q$ be its
Quillen metric. Then in $\widehat{CH}^1(Y)_\mathbb{Q}$

$$\hat c_1(\lambda(E), h_Q) = f_*\Bigl( \widehat{\mathrm{ch}}(\bar E) \, \widehat{\mathrm{Td}}(f) -
a\bigl( \mathrm{ch}(E_\mathbb{C}) \, \mathrm{Td}(Tf_\mathbb{C}) \, R(Tf_\mathbb{C}) \bigr)
\Bigr)^{(1)}.$$

The terms are the following.

- The Quillen metric: on a fibre $X_y$, of complex dimension $d$, let $\omega_0$ be the Kähler form
  of the chosen metric $h_f$ on $Tf_\mathbb{C}$ (not the metric of $\bar E$), given in local
  coordinates by $\omega_0 = \sum_{\alpha, \beta} \frac{i}{2\pi} h_f(\partial/\partial z_\alpha,
  \partial/\partial z_\beta) \, dz_\alpha \wedge d\bar z_\beta$, and give the spaces $A^{0,q}(X_y,
  E)$ of $E$-valued forms of type $(0, q)$ the scalar product $\langle s, t \rangle = \int_{X_y}
  \langle s(x), t(x) \rangle \, \omega_0^d / d!$. Hodge theory identifies $H^q(X_y, E)$ with the
  kernel of the Laplacian $\Delta_q = \bar\partial \bar\partial^* + \bar\partial^* \bar\partial$,
  which induces the $L^2$ metric $h_{L^2}$ on $\lambda(E)_y$. The zeta function $\zeta_q(s) =
  \operatorname{Tr}(\Delta_q^{-s} \mid (\ker \Delta_q)^\perp)$ converges for $\operatorname{Re} s >
  d$ and extends meromorphically to $\mathbb{C}$, regular at $0$; the Ray–Singer analytic torsion is
  $T(X_y, E) = \sum_{q \ge 0} (-1)^{q+1} q \, \zeta_q'(0)$, and $h_Q = h_{L^2} \exp(T(X_y, E))$.
  Bismut, Gillet and Soulé showed that $h_Q$ is smooth on $\lambda(E)_\mathbb{C}$.
- $\hat c_1(\lambda(E), h_Q) \in \widehat{CH}^1(Y)$ is the class of the hermitian line bundle
  $(\lambda(E), h_Q)$, $\widehat{\mathrm{ch}}(\bar E) \in \widehat{CH}^*(X)_\mathbb{Q}$ is the
  arithmetic Chern character, and $\widehat{\mathrm{Td}}(f) \in \widehat{CH}^*(X)_\mathbb{Q}$ is the
  arithmetic Todd class of $f$, built from a factorization of $f$ through $Y \times \mathbb{P}^N$
  and depending only on the metric on $Tf_\mathbb{C}$; when $f$ is smooth, the introduction of
  Gillet and Soulé's paper states the formula with the arithmetic Todd class
  $\widehat{\mathrm{Td}}(Tf, h_f)$ of the hermitian relative tangent bundle.
- $\mathrm{ch}(E_\mathbb{C})$ and $\mathrm{Td}(Tf_\mathbb{C})$ are the usual Chern character and
  Todd class in the real cohomology $H^*(X(\mathbb{C}), \mathbb{R})$, and $R$ is the additive
  characteristic class with values in real cohomology that is contravariant, additive on exact
  sequences, and given on a holomorphic line bundle $L$ by

    $$R(L) = \sum_{m \text{ odd},\, m \ge 1} \Bigl( 2\zeta'(-m) + \Bigl( 1 + \frac12 + \dots +
    \frac1m \Bigr) \zeta(-m) \Bigr) \frac{c_1(L)^m}{m!},$$

  with $\zeta$ the Riemann zeta function.
- The product $\mathrm{ch}(E_\mathbb{C}) \mathrm{Td}(Tf_\mathbb{C}) R(Tf_\mathbb{C})$ is represented
  by characteristic forms; its real component of type $(j, j)$, of the parity required by
  $F_\infty$, is mapped by the map $a$ of the arithmetic Chow groups to
  $\widehat{CH}^{j+1}(X)_\mathbb{Q}$, changing the form by an exact form not changing the class. For
  $f$ of relative dimension $d$, the push-forward maps $\widehat{CH}^k(X)_\mathbb{Q}$ to
  $\widehat{CH}^{k-d}(Y)_\mathbb{Q}$, and $\alpha^{(1)}$ is the component of degree one of the
  pushed-forward class. The class in parentheses has components of several degrees (its degree-zero
  part is $\operatorname{rk} E$); only its component in $\widehat{CH}^{d+1}(X)_\mathbb{Q}$
  contributes, and for the correction term this is the image under $a$ of its forms of type $(d,
  d)$. The term $R$ is applied once, to $Tf_\mathbb{C}$, and is subtracted.

This is formula (13) of Gillet and Soulé's Theorem 7, stated for every arithmetic ring, as an
identity in $\widehat{CH}^1(Y)_\mathbb{Q}$ only. The same theorem contains two further forms, for a
good arithmetic ring, that is, one that is equicodimensional and Jacobson.

- Formula (12): $f$ projective, a local complete intersection morphism, smooth on the generic fibre,
  $X$ and $Y$ not necessarily regular, $\bar E$ a hermitian vector bundle; for $\alpha \in
  \widehat{CH}_p(Y)_\mathbb{Q}$, $p \ge 1$, in arithmetic Chow groups graded by dimension, one caps
  the right-hand side with $f^* \alpha$, pushes forward and takes the component of dimension $p -
  1$, which equals $\hat c_1(\lambda(E), h_Q) \cap \alpha$.
- Formula (11): $Y$ regular, $X$ not necessarily regular, $\bar{\mathcal{F}}$ a hermitian coherent
  sheaf on $X$, locally free on the generic fibre with a smooth metric invariant under conjugation
  on the resulting vector bundle, and metrics also on $TX(\mathbb{C})$ and $TY(\mathbb{C})$. Its
  right-hand side is $f_*\bigl( \tau(\mathcal{F}) + a(\mathrm{ch}(\mathcal{F}_\mathbb{C})
  \widetilde{\mathrm{Td}}(f)) - a(\mathrm{ch}(\mathcal{F}_\mathbb{C}) \mathrm{Td}(Tf_\mathbb{C})
  R(Tf_\mathbb{C})) \bigr)^{(1)}$, with the homological Riemann–Roch class $\tau(\mathcal{F})$ of
  Gillet and Soulé's Definition 7, defined through an embedding of $X$ into a regular arithmetic
  variety from the arithmetic Chern character with supports, a Todd factor and a secondary term
  (Definitions 6–7, Lemma 25, Theorem 5), and with $\widetilde{\mathrm{Td}}(f)$ the secondary class
  of the exact sequence $0 \to Tf_\mathbb{C} \to TX(\mathbb{C}) \to f^* TY(\mathbb{C}) \to 0$,
  distinct from the secondary term already contained in $\tau(\mathcal{F})$. Gillet and Soulé write
  its left-hand side $\tau(\lambda(\mathcal{F}), h_Q)^{(1)}$, the determinant of cohomology being a
  **graded** line (§4.1.2, p. 523; for Knudsen and Mumford the determinant of a vector bundle $E$ is
  the pair $(\Lambda^{\max} E, \operatorname{rk} E)$). This page does not identify that symbol with
  Definition 7 applied to the underlying ungraded line, for which the identity would fail: for $f =
  \mathrm{id}$ on $Y = \mathbb{P}^1_\mathbb{Z}$, $\mathcal{F} = \mathcal{O}^2$ and identical trivial
  metrics, the relative tangent bundle is zero and the tangent sequence splits isometrically, but on
  $\mathbb{P}^1_\mathbb{Q}$, forgetting the metrics, the underlying line $\mathcal{O}$ gives
  $\mathrm{Td}_1(Y) = H$ while $\tau(\mathcal{F})^{(1)}$ gives $2H$, with $H = c_1(\mathcal{O}(1))$;
  an expression sensitive to the rank, of the shape $\hat c_1(\lambda, h_Q) + \operatorname{rk}(Rf_*
  \mathcal{F})\, \widehat{\mathrm{Td}}{}_1(Y)$, would be needed, and none is sourced here. The
  explicit coherent formula stated here is the specialisation to $Y = \operatorname{Spec}
  \mathbb{Z}$, (14)–(15), where $\mathrm{Td}_1(Y) = 0$, with $TX(\mathbb{C}) = Tf_\mathbb{C}$
  carrying the same Kähler metric as in the construction of $h_Q$: the arithmetic Euler
  characteristic

    $$\chi_Q(\bar{\mathcal{F}}) = \sum_q (-1)^q \bigl( \log \# H^q(X, \mathcal{F})_{\mathrm{tors}} - \log \operatorname{covol}_{L^2}\bigl( H^q(X, \mathcal{F}) / H^q(X, \mathcal{F})_{\mathrm{tors}} \bigr) \bigr) - \frac{T(X(\mathbb{C}), \mathcal{F}_\mathbb{C})}{2},$$

  the covolume being that of the lattice in the real cohomology fixed by complex conjugation, with
  one correction by half the analytic torsion $T$ of the convention above, equals $\bigl[ f_*\bigl(
  \tau(\mathcal{F}) - a(\mathrm{ch}(\mathcal{F}_\mathbb{C}) \mathrm{Td}(Tf_\mathbb{C})
  R(Tf_\mathbb{C})) \bigr) \bigr]^{(1)}$ in $\widehat{CH}^1(\operatorname{Spec} \mathbb{Z}) =
  \mathbb{R}$ (pp. 525 and 535, (37)); $X$ need not be regular. Gillet and Soulé correct in 4.2.5 an
  earlier announcement of (11) that omitted terms.

Gillet and Soulé conjectured formula (13) for smooth projective morphisms of regular arithmetic
varieties in their paper on the arithmetic Todd genus (Conjecture 1.3 there). Their proof factors
$f$ as a closed immersion $i \colon X \to \mathbb{P}^N_Y$ followed by the projection $g \colon
\mathbb{P}^N_Y \to Y$, over the common base $Y$. One chooses a Kähler metric on the ambient space
and a resolution of $i_* E$ by hermitian vector bundles on $\mathbb{P}^N_Y$ whose metrics satisfy
Bismut's condition (A) with respect to the metrics induced on $X$ and on the normal bundle of $i$.
Bismut and Lebeau's immersion formula computes, on the compact complex fibres, the logarithm of the
squared Quillen norm of the canonical isomorphism between the determinants of cohomology of $E$ and
of the resolution ((31)–(32)). Separately, Bismut, Gillet and Soulé's Theorem 4.13 proves the
corresponding identity of arithmetic classes on the base for smooth projective morphisms of regular
arithmetic varieties ((33)); Gillet and Soulé extend the proof of (33) to projective local complete
intersection morphisms smooth on the generic fibre (4.2.3), and change of metrics on $Tf_\mathbb{C}$
is controlled by the anomaly formulas. For the coherent form (11) on a possibly non-l.c.i. $X$ they
use instead Lemma 21 (p. 512) and 4.2.2 (pp. 528–531). This reduces the theorem to $g$. For $g$ the
defect of the formula is additive, does not depend on the metrics, and vanishes on virtual bundles
supported away from the generic fibre by algebraic Riemann–Roch; using the generators
$\mathcal{O}(n)$, the identity $\delta(E \otimes g^* G) = \operatorname{rk}(G)\, \delta(E)$ for the
defect $\delta$ (p. 532), base change from $\mathbb{P}^N_\mathbb{Z}$ and the exact sequences of
hyperplanes, it reduces to the trivial bundle on $\mathbb{P}^N_\mathbb{Z}$, the case proved in the
paper on the arithmetic Todd genus (its Theorem 2.1.1), 4.2.1–4.2.4.

## Depends on

- [Arithmetic characteristic classes of hermitian vector bundles](arithmetic-chern-classes.md), for
  $\widehat{\mathrm{ch}}(\bar E)$, $\widehat{\mathrm{Td}}(f)$, the Chern character with supports and the
  class $\tau$
- [Arithmetic Chow groups](arithmetic-chow-group.md), for the map $a$
- [Arithmetic intersection product](arithmetic-intersection-product.md)
- [Arithmetic degree and arithmetic intersection numbers](arithmetic-intersection-numbers.md), for $\hat c_1$ of a hermitian line bundle and the push-forward $f_*$
- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md)
- [Analytic torsion and Quillen metrics](analytic-torsion-and-quillen-metrics.md), for the Quillen metric $h_Q$ and its smoothness

## Proof depends on

- [Analytic torsion and Quillen metrics](analytic-torsion-and-quillen-metrics.md), for the immersion
  formula of Bismut and Lebeau, the arithmetic identity of Bismut, Gillet and Soulé's Theorem 4.13 and
  its extension by Gillet and Soulé to l.c.i. morphisms, and the case of the trivial bundle on
  $\mathbb{P}^N_\mathbb{Z}$ from the paper on the arithmetic Todd genus
- [Arithmetic characteristic classes of hermitian vector bundles](arithmetic-chern-classes.md), for
  Lemma 21, the comparison of Chern characters with supports used for (11)

## Sources

- H. Gillet and C. Soulé, "An arithmetic Riemann–Roch theorem", Invent. Math. 110 (1992), 473–543,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0110>: introduction, formula (1) and the class
  $R$, pp. 473–474; §2.1 (good arithmetic rings, quasi-projective arithmetic varieties, Chow groups
  graded by dimension), pp. 484–485; Definition 5, p. 499; 2.6.2 and Proposition 1 (the arithmetic
  Todd class $\widehat{\mathrm{Td}}(f)$ of a local complete intersection morphism smooth on the
  generic fibre, pp. 503–504); §3.1, Definition 6 (the arithmetic Chern character with supports), p.
  510, Corollary 3, pp. 510–511, and Lemma 21, p. 512; §3.2, Definition 7 (the class $\tau$), p.
  516, Lemma 25, Theorem 5, p. 517, and Theorem 6 (i), (iii), p. 521; 4.1.1–4.1.3 (Quillen metric,
  setting, the class $R$), pp. 522–524; Theorem 7 with formulas (11)–(13), pp. 524–525; 4.1.5 with
  (14)–(15), p. 525; the proof 4.2.1–4.2.4, pp. 528–533 (4.2.2, pp. 528–531; (31)–(33), pp. 531–532;
  4.2.3, p. 532: comparison with Bismut, Gillet and Soulé's Theorem 4.13 and its extension to l.c.i.
  morphisms smooth on the generic fibre; 4.2.4, p. 532); 4.2.5, p. 533; (37), p. 535.
- H. Gillet and C. Soulé, "Analytic torsion and the arithmetic Todd genus", with an appendix by D.
  Zagier, Topology 30 (1991), 21–54: Conjecture 1.3, pp. 25–26; Theorem 1.4 (i), (iii), p. 26;
  Theorem 2.1.1 and Remarks 2.1.2, p. 29.
- J.-M. Bismut, H. Gillet and C. Soulé, "Complex immersions and Arakelov geometry", in *The
  Grothendieck Festschrift I*, Birkhäuser, 1990, 249–331: §4 (f), Theorem 4.13, pp. 327–329 (smooth
  projective maps of regular arithmetic varieties).
- J.-M. Bismut and G. Lebeau, "Complex immersions and Quillen metrics", Publ. Math. IHÉS 74 (1991),
  1–298: Theorem 0.1 and (0.5), pp. 1–3, and condition (A).
- C. Soulé, with D. Abramovich, J.-F. Burnol and J. Kramer, *Lectures on Arakelov Geometry*,
  Cambridge Studies in Advanced Mathematics 33, Cambridge University Press, 1992: chapter "The
  Arithmetic Riemann–Roch–Grothendieck Theorem" (pp. 157–168).
