# Faltings height of an elliptic curve in terms of its discriminant and periods

Let $L$ be a number field with ring of integers $\mathcal{O}_L$, let $E$ be an elliptic curve over $L$,
let $h_{\mathrm{Fal}}(E/L)$ be its
[Faltings height over $L$](faltings-height-over-the-field-of-definition.md), computed with the
[finite-type Néron model](../../not-yet-classified/neron-models/finite-type-neron-model.md) of $E$ over $\mathcal{O}_L$, with its
[group structure](../../not-yet-classified/neron-models/group-structure.md), and the metrics $\frac{i}{2} \int s \wedge \bar s$, and let
$\Delta_{E/L} \subseteq \mathcal{O}_L$ be its [minimal discriminant](minimal-discriminant.md). For
$\tau$ in the upper half-plane $\mathbb{H}$ let

$$\Delta(\tau) = g_2(\tau)^3 - 27 g_3(\tau)^2 = (2\pi)^{12} \eta(\tau)^{24}
  = (2\pi)^{12} \, q \prod_{n \ge 1} (1 - q^n)^{24}, \qquad q = e^{2\pi i \tau},$$

the discriminant of the lattice $\mathbb{Z} + \mathbb{Z}\tau$, with the second equality
[Jacobi's product formula](../../../NumberTheory/modular-forms-q-series/modular-forms/lattice-discriminant-eta-product.md).
For each embedding $\sigma : L \to \mathbb{C}$ choose $\tau_\sigma \in \mathbb{H}$ with
$E_\sigma(\mathbb{C}) \cong \mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau_\sigma)$ as complex Lie groups, which
the [complex uniformization](complex-uniformization.md) provides.

**Theorem** (Silverman, Proposition 1.1; Barquero-Sanchez, Cadwallader, Cannon, Genao and Masri,
equation (6.2))**.** For every elliptic curve $E$ over a number field $L$,

$$h_{\mathrm{Fal}}(E/L) = \frac{\log N_{L/\mathbb{Q}}(\Delta_{E/L})}{12 [L : \mathbb{Q}]}
  - \frac{1}{12 [L : \mathbb{Q}]} \sum_{\sigma : L \to \mathbb{C}}
    \log \bigl( |\Delta(\tau_\sigma)| \, (\operatorname{Im} \tau_\sigma)^6 \bigr),$$

where $N_{L/\mathbb{Q}}(\Delta_{E/L}) = \# (\mathcal{O}_L / \Delta_{E/L})$. Equivalently,
$h_{\mathrm{Fal}}(E/L) = \frac{\log N_{L/\mathbb{Q}}(\Delta_{E/L})}{12 [L : \mathbb{Q}]} - \log (2\pi)
- \frac{1}{12 [L : \mathbb{Q}]} \sum_{\sigma} \log \bigl( |\eta(\tau_\sigma)|^{24} (\operatorname{Im} \tau_\sigma)^6 \bigr)$.
No semistability hypothesis is made. The choices of $\tau_\sigma$ differ by elements of
$\mathrm{SL}_2(\mathbb{Z})$, under which
[$|\Delta(\tau)| (\operatorname{Im} \tau)^6$ is invariant](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-group-and-congruence-subgroups/discriminant-im-pow-six-invariant.md),
so the right-hand side does not depend on them.

*Proof* (Silverman, pp. 254–256). Let $\beta_E = \Delta_W \, \omega_W^{\otimes 12}$ be the element
of $H^0(E, \Omega^1_{E/L})^{\otimes 12}$ given by any Weierstrass equation $W$ of $E$, which does not
depend on $W$. Computing $12 [L : \mathbb{Q}] \, h_{\mathrm{Fal}}(E/L)$ as the arithmetic degree of
$\bar\omega^{\otimes 12}$ with the rational section $\beta_E$, the finite places contribute
[$\log N_{L/\mathbb{Q}}(\Delta_{E/L})$](faltings-height-finite-places.md) and the embedding $\sigma$
contributes
[$-\log(|\Delta(\tau_\sigma)| (\operatorname{Im} \tau_\sigma)^6)$](faltings-height-infinite-places.md).

Silverman's list of notation prints $\Delta(\tau) = (2\pi)^{-12} q \prod_{n \ge 1} (1 - q^n)^{24}$, but
his proof takes $\Delta(\tau_v) = g_2(\tau_v)^3 - 27 g_3(\tau_v)^2$, the discriminant of the
Weierstrass equation $Y^2 = 4X^3 - g_2(\tau_v) X - g_3(\tau_v)$ of
$\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau_v)$, and it is with this value that he writes the invariant
section $\beta = \Delta(\tau)(dz)^{\otimes 12}$ on $\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)$ and
computes $\frac{i}{2} \int \alpha \wedge \bar\alpha = |\Delta(\tau)|^{1/6} \operatorname{Im}(\tau)$ for
$\alpha = \Delta(\tau)^{1/12} dz$; by Jacobi's product formula, $g_2^3 - 27 g_3^2 = (2\pi)^{12} \eta^{24}$.
Barquero-Sanchez, Cadwallader, Cannon, Genao and Masri restate the theorem with
$\Delta = (2\pi)^{12} \eta^{24}$, and it is with this $\Delta$ that the theorem agrees with Deligne's
values for the stable height, as [Deligne's formula](stable-height-of-an-elliptic-curve.md) records.
The theorem computes the height over $L$, not the stable height; the two are compared on
[a page of their own](faltings-height-and-stable-height.md).

## Depends on

- [Faltings height of an elliptic curve over its field of definition](faltings-height-over-the-field-of-definition.md),
  for $h_{\mathrm{Fal}}(E/L)$
- [Finite-type Néron model](../../not-yet-classified/neron-models/finite-type-neron-model.md), over
  $\mathcal{O}_L$ and its fraction field $L$, for the Néron model $\mathcal{E}$ through which
  $h_{\mathrm{Fal}}(E/L)$ is defined
- [Group structure on a Néron model](../../not-yet-classified/neron-models/group-structure.md), for the
  group law of $\mathcal{E}$ and its zero section $\varepsilon$
- [Minimal discriminant of an elliptic curve over a number field](minimal-discriminant.md), for
  $\Delta_{E/L}$
- [Jacobi's product formula for the discriminant of a lattice](../../../NumberTheory/modular-forms-q-series/modular-forms/lattice-discriminant-eta-product.md),
  for $\Delta(\tau) = g_2(\tau)^3 - 27 g_3(\tau)^2 = (2\pi)^{12} \eta(\tau)^{24}$
- [Complex uniformization of elliptic curves](complex-uniformization.md), for the existence of the
  $\tau_\sigma$ and for items 3 and 4, by which they differ by elements of $\mathrm{SL}_2(\mathbb{Z})$
- [Invariance of $|\Delta(\tau)| (\operatorname{Im} \tau)^6$ under the modular group](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-group-and-congruence-subgroups/discriminant-im-pow-six-invariant.md),
  for the independence of the right-hand side from the $\tau_\sigma$

## Proof depends on

- [Faltings height of an elliptic curve over its field of definition](faltings-height-over-the-field-of-definition.md),
  for $12 [L : \mathbb{Q}] \, h_{\mathrm{Fal}}(E/L) = \widehat{\deg}(\bar\omega^{\otimes 12})$ computed
  with a rational section
- [The invariant differential of a Weierstrass equation](invariant-differential-of-a-weierstrass-equation.md),
  for the rational section $\beta_E$
- [The finite places in Silverman's formula for the Faltings height](faltings-height-finite-places.md)
- [The infinite places in Silverman's formula for the Faltings height](faltings-height-infinite-places.md)

## Sources

- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: the minimal discriminant $\Delta_{E/K}$ and
  $\Delta(\tau)$ in the list of notation, p. 254; Proposition 1.1, p. 254, with Remark 1.2 (the height
  is not the stabilized one; independence of the $\tau_v$) and the proof, pp. 254–256 (the minimal
  Weierstrass equation (2) at a finite place, with $v(\Delta_v) = v(\Delta_{E/K})$, p. 255; the
  Weierstrass equation (3), $Y_v^2 = 4X_v^3 - g_2(\tau_v) X_v - g_3(\tau_v)$, and below it
  $\Delta_v = g_2(\tau_v)^3 - 27 g_3(\tau_v)^2 = \Delta(\tau_v)$, p. 255; the section
  $\beta = \Delta \cdot (dx / (2y + a_1 x + a_3))^{\otimes 12}$ and the contribution of the finite
  places, p. 255; the archimedean contribution
  $-(n_v / 12 [K : \mathbb{Q}]) \log (|\Delta(\tau_v)| \operatorname{Im}(\tau_v)^6)$, p. 256). The proposition
  sums over the archimedean places $v$ with $n_v = [K_v : \mathbb{Q}_v]$, which is the sum over the
  embeddings, since conjugate embeddings give the same term.
- A. Barquero-Sanchez, L. Cadwallader, O. Cannon, T. Genao and R. Masri, "Faltings heights of CM
  elliptic curves and special Gamma values", Res. Number Theory 3 (2017), art. 13,
  <https://doi.org/10.1007/s40993-017-0077-7>: the definition of $h_{\mathrm{Fal}}(E/L)$, p. 1, "normalized
  as in Silverman [16] (who in turn uses the same normalization as Faltings [6, p. 14])"; the stable
  height and its invariance under semistable reduction, and (1.2),
  $h_{\mathrm{geom}}(E) = h^{\mathrm{stab}}_{\mathrm{Fal}}(E/L) + \frac{1}{2} \log \pi$, p. 2; equation (6.2), p. 14, the theorem with
  $\Delta(z) = (2\pi)^{12} \eta(z)^{24}$, stated as Silverman's Proposition 1.1, and its form (6.3)
  with $-\log(2\pi)$ and $F(z) = \sqrt{\operatorname{Im}(z)} |\eta(z)|^2$ of (3.2), p. 5.
- P. Deligne, "Preuve des conjectures de Tate et de Shafarevitch [d'après G. Faltings]", Séminaire
  Bourbaki, exposé 616 (1983/84), Astérisque 121–122 (1985), 25–41,
  <http://www.numdam.org/item/SB_1983-1984__26__25_0/>: pp. 25–26, §1.1, the absolute values
  $\| \cdot \|_v$ on $k$, which satisfy the product formula, and
  $\#(L_{\mathcal{O}} / \mathcal{O} \cdot \ell) = \prod_{v \text{ fini}} \| \ell \|_v^{-1}$ for an
  $\mathcal{O}$-form $L_{\mathcal{O}}$ of a $k$-vector space of rank one and $\ell \in L_{\mathcal{O}}$;
  for the $\mathcal{O}$-form $\mathcal{O}_k$ of $k$ itself this gives
  $\| x \|_v = (N\mathfrak{p})^{-\operatorname{ord}_{\mathfrak{p}}(x)}$, the absolute values of Deligne's
  formula; §1.2, pp. 26–27, the height $h(A)$ and the geometric height; Remarque 1.5, pp. 28–29, the formula for the geometric height of an elliptic curve
  and its minimum $h_{\min} \approx -0.749$.
