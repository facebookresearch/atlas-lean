# Arithmetic Riemann–Roch theorem

Let $A$ be an arithmetic ring with fraction field $F$, and let $f \colon X \to Y$ be a projective
morphism of regular arithmetic varieties over $A$ whose restriction $X_F \to Y_F$ to the generic
fibres is smooth. Choose on the relative tangent bundle $Tf_\mathbb{C}$ of $X(\mathbb{C}) \to
Y(\mathbb{C})$ a hermitian metric, invariant under complex conjugation, whose restriction to every
fibre $X_y = f^{-1}(y)$, $y \in Y(\mathbb{C})$, is Kähler, and let $\bar E$ be a hermitian vector
bundle on $X$. Let $\lambda(E) = \det Rf_* E$ be the determinant of cohomology, a line bundle on $Y$
whose fibre at $y \in Y(\mathbb{C})$ is $\bigotimes_{q \ge 0} \det H^q(X_y, E)^{(-1)^q}$, and let
$h_Q$ be its Quillen metric. Then in $\widehat{CH}^1(Y)_\mathbb{Q}$
$$\hat c_1(\lambda(E), h_Q) = f_*\Bigl( \widehat{\mathrm{ch}}(\bar E) \, \widehat{\mathrm{Td}}(f) -
a\bigl( \mathrm{ch}(E_\mathbb{C}) \, \mathrm{Td}(Tf_\mathbb{C}) \, R(Tf_\mathbb{C}) \bigr)
\Bigr)^{(1)}.$$

The terms are the following.

- The Quillen metric: on a fibre $X_y$, of complex dimension $d$, let $\omega_0$ be the Kähler form
  of the metric, given in local coordinates by $\omega_0 = \sum_{\alpha, \beta} \frac{i}{2\pi}
  h(\partial/\partial z_\alpha, \partial/\partial z_\beta) \, dz_\alpha \wedge d\bar z_\beta$, and
  give the spaces $A^{0,q}(X_y, E)$ of $E$-valued forms of type $(0, q)$ the scalar product
  $\langle s, t \rangle = \int_{X_y} \langle s(x), t(x) \rangle \, \omega_0^d / d!$. Hodge theory
  identifies $H^q(X_y, E)$ with the kernel of the Laplacian $\Delta_q = \bar\partial
  \bar\partial^* + \bar\partial^* \bar\partial$, which induces the $L^2$ metric $h_{L^2}$ on
  $\lambda(E)_y$. The zeta function $\zeta_q(s) = \operatorname{Tr}(\Delta_q^{-s} \mid
  (\ker \Delta_q)^\perp)$ converges for $\operatorname{Re} s > d$ and extends meromorphically to
  $\mathbb{C}$, regular at $0$; the Ray–Singer analytic torsion is $T(X_y, E) = \sum_{q \ge 0}
  (-1)^{q+1} q \, \zeta_q'(0)$, and $h_Q = h_{L^2} \exp(T(X_y, E))$. Bismut, Gillet and Soulé showed
  that $h_Q$ is smooth on $\lambda(E)_\mathbb{C}$.
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
- $a$ maps real cohomology classes to $\widehat{CH}^*(X)_\mathbb{Q}$ through the map $a$ of the
  arithmetic Chow groups, $f_* \colon \widehat{CH}^*(X)_\mathbb{Q} \to \widehat{CH}^*(Y)_\mathbb{Q}$
  is the push-forward, and $\alpha^{(1)}$ is the component of degree one.

This is formula (13) of Gillet and Soulé's Theorem 7, which they state for every arithmetic ring.
The same theorem contains a version for a local complete intersection morphism, smooth on the
generic fibre, with homological arithmetic Chow groups and a good arithmetic ring (formula (12)),
and a version for a good arithmetic ring, a regular $Y$ and a hermitian coherent sheaf on $X$
(formula (11)); for $Y = \operatorname{Spec} \mathbb{Z}$ the latter computes the arithmetic Euler
characteristic of a hermitian coherent sheaf (4.1.5). Gillet and Soulé had conjectured the formula
in their paper on the arithmetic Todd genus. Their proof factors $f$ as a closed immersion
$i \colon X \to \mathbb{P}^N_Y$ followed by the projection $g \colon \mathbb{P}^N_Y \to Y$: for a
resolution of $i_* E$ by vector bundles with metrics, the difference of the left-hand sides was
computed by Bismut and Lebeau and the corresponding alternating sum of right-hand sides by Bismut,
Gillet and Soulé, which reduces the theorem to $g$; for $g$ it reduces to the trivial bundle on
$\mathbb{P}^N_\mathbb{Z}$, the case proved in the paper on the arithmetic Todd genus (introduction,
pp. 473–474, and 4.2).

## Depends on

- [Arithmetic characteristic classes of hermitian vector bundles](arithmetic-chern-classes.md), for $\widehat{\mathrm{ch}}(\bar E)$ and $\widehat{\mathrm{Td}}(f)$
- [Arithmetic Chow groups](arithmetic-chow-group.md), for the map $a$
- [Arithmetic intersection product](arithmetic-intersection-product.md)
- [Arithmetic degree and arithmetic intersection numbers](arithmetic-intersection-numbers.md), for $\hat c_1$ of a hermitian line bundle and the push-forward $f_*$
- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md)
- [Analytic torsion and Quillen metrics](analytic-torsion-and-quillen-metrics.md), for the Quillen metric $h_Q$ and its smoothness

## Proof depends on

- [Analytic torsion and Quillen metrics](analytic-torsion-and-quillen-metrics.md), for the immersion formula of Bismut and Lebeau, Bismut, Gillet and Soulé's Theorem 4.13, and the case of the trivial bundle on $\mathbb{P}^N_\mathbb{Z}$ from the paper on the arithmetic Todd genus

## Sources

- H. Gillet and C. Soulé, "An arithmetic Riemann–Roch theorem", Invent. Math. 110 (1992), 473–543,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0110>: introduction, formula (1) and the class
  $R$ (pp. 473–474); 2.6.2 and Proposition 1 (the arithmetic Todd class $\widehat{\mathrm{Td}}(f)$
  of a local complete intersection morphism smooth on the generic fibre, pp. 503–504); 4.1.1–4.1.3
  (Quillen metric, setting, the class $R$, pp. 522–524); Theorem 7 with formulas (11)–(13)
  (pp. 524–525); 4.1.5 (p. 525); 4.2.5 (p. 533).
- C. Soulé, with D. Abramovich, J.-F. Burnol and J. Kramer, *Lectures on Arakelov Geometry*,
  Cambridge Studies in Advanced Mathematics 33, Cambridge University Press, 1992: chapter "The
  Arithmetic Riemann–Roch–Grothendieck Theorem" (pp. 157–168).
