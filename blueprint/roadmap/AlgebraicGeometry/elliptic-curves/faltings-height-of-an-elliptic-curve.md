# Faltings height of an elliptic curve in terms of its discriminant and periods

This node is still to be broken down: the statement is precise, but the definitions it uses and its
proof are not.

Let $L$ be a number field with ring of integers $\mathcal{O}_L$, let $E$ be an elliptic curve over
$L$, let $\mathcal{E}$ be its Néron model over $\mathcal{O}_L$, defined as the
[Néron model](../abelian-varieties/neron-model.md) over a discrete valuation ring with
$\mathcal{O}_L$ in place of the discrete valuation ring: the smooth separated group scheme of finite
type over $\mathcal{O}_L$ with generic fibre $E$ that represents the functor
$S \mapsto \operatorname{Hom}_L(S \times_{\operatorname{Spec} \mathcal{O}_L} \operatorname{Spec} L, E)$
on smooth $\mathcal{O}_L$-schemes. Let $\varepsilon$ be its zero section, and let
$\omega = \varepsilon^* \Omega^1_{\mathcal{E}/\mathcal{O}_L}$, an invertible $\mathcal{O}_L$-module
with $\omega \otimes_{\sigma} \mathbb{C} = H^0(E_\sigma, \Omega^1)$ for every embedding
$\sigma : L \to \mathbb{C}$. The **Faltings height of $E/L$** is

$$h_{\mathrm{Fal}}(E/L) = \frac{1}{[L : \mathbb{Q}]} \Bigl( \log \# \bigl( \omega / s \mathcal{O}_L \bigr)
  - \frac{1}{2} \sum_{\sigma : L \to \mathbb{C}} \log \Bigl( \frac{i}{2} \int_{E_\sigma(\mathbb{C})} s \wedge \bar s \Bigr) \Bigr)$$

for any nonzero $s \in \omega$; it does not depend on $s$. This is Faltings' original
normalization, the one of the [stable Faltings height](../abelian-varieties/stable-faltings-height/faltings-height.md)
in dimension one, but computed with the Néron model of $E$ over $L$ itself, with no extension of $L$.

Let $\Delta_{E/L} \subseteq \mathcal{O}_L$ be the minimal discriminant ideal of $E/L$: its valuation
at each maximal ideal $\mathfrak{p}$ is the valuation of the discriminant of a Weierstrass equation
for $E$ that is minimal at $\mathfrak{p}$. For $\tau$ in the upper half-plane $\mathbb{H}$ let

$$\Delta(\tau) = g_2(\tau)^3 - 27 g_3(\tau)^2 = (2\pi)^{12} \eta(\tau)^{24}
  = (2\pi)^{12} \, q \prod_{n \ge 1} (1 - q^n)^{24}, \qquad q = e^{2\pi i \tau},$$

the discriminant of the lattice $\mathbb{Z} + \mathbb{Z}\tau$, with the second equality
[Jacobi's product formula](../../NumberTheory/modular-forms-q-series/modular-forms/lattice-discriminant-eta-product.md).
For each embedding $\sigma : L \to \mathbb{C}$ choose $\tau_\sigma \in \mathbb{H}$ with
$E_\sigma(\mathbb{C}) \cong \mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau_\sigma)$ as complex Lie groups.

**Theorem** (Silverman, Proposition 1.1; Barquero-Sanchez, Cadwallader, Cannon, Genao and Masri,
equation (6.2))**.** For every elliptic curve $E$ over a number field $L$,

$$h_{\mathrm{Fal}}(E/L) = \frac{\log N_{L/\mathbb{Q}}(\Delta_{E/L})}{12 [L : \mathbb{Q}]}
  - \frac{1}{12 [L : \mathbb{Q}]} \sum_{\sigma : L \to \mathbb{C}}
    \log \bigl( |\Delta(\tau_\sigma)| \, (\operatorname{Im} \tau_\sigma)^6 \bigr),$$

where $N_{L/\mathbb{Q}}(\Delta_{E/L}) = \# (\mathcal{O}_L / \Delta_{E/L})$. Equivalently,
$h_{\mathrm{Fal}}(E/L) = \frac{\log N_{L/\mathbb{Q}}(\Delta_{E/L})}{12 [L : \mathbb{Q}]} - \log (2\pi)
- \frac{1}{12 [L : \mathbb{Q}]} \sum_{\sigma} \log \bigl( |\eta(\tau_\sigma)|^{24} (\operatorname{Im} \tau_\sigma)^6 \bigr)$.
No semistability hypothesis is made. Since $\Delta$ is a modular form of weight $12$ for
$\mathrm{SL}_2(\mathbb{Z})$, $|\Delta(\tau)| (\operatorname{Im} \tau)^6$ is invariant under
$\mathrm{SL}_2(\mathbb{Z})$, so the right-hand side does not depend on the choice of the
$\tau_\sigma$.

**Relation with the stable height.** Write $h_F(E)$ for the
[stable Faltings height](../abelian-varieties/stable-faltings-height/faltings-height.md). Then
$h_{\mathrm{Fal}}(E/L) \ge h_F(E)$, with equality if and only if $E$ has semistable reduction at every
finite place of $L$. So $h_F(E) = h_{\mathrm{Fal}}(E/L')$ for any finite extension $L'/L$ over which
$E$ has semistable reduction everywhere, and when $E$ has good reduction at every finite place of
$L$ the norm term vanishes and

$$h_F(E) = - \frac{1}{12 [L : \mathbb{Q}]} \sum_{\sigma : L \to \mathbb{C}}
  \log \bigl( |\Delta(\tau_\sigma)| \, (\operatorname{Im} \tau_\sigma)^6 \bigr).$$

In general, for $E$ over a number field $k$ with $j$-invariant $j$, with $\tau_\iota \in \mathbb{H}$
of $j$-invariant $\iota(j)$ for each embedding $\iota : k \to \mathbb{C}$, and with
$\| \cdot \|_v$ the normalized absolute values at the finite places $v$ of $k$,

$$[k : \mathbb{Q}] \, h_F(E) = \frac{1}{12} \sum_{v \text{ finite}} \log \max(1, \| j \|_v)
  - \frac{1}{12} \sum_{\iota : k \to \mathbb{C}} \log \bigl( |\Delta(\tau_\iota)| \, (\operatorname{Im} \tau_\iota)^6 \bigr).$$

Deligne states this for the height $h_{\mathrm{geom}}(E) = h_F(E) + \frac{1}{2} \log \pi$, defined with
the metric $\frac{1}{2\pi} \int |s \wedge \bar s|$, as
$\exp([k : \mathbb{Q}] h_{\mathrm{geom}}(E)) = \prod_{\iota} V(\iota j)^{-1/2}
\prod_{v \text{ finite}} \max(1, \|j\|_v)^{1/12}$, where
$V(j(\tau)) = \frac{1}{2\pi} \int_{\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)} |\alpha \wedge \bar\alpha|
= 4\pi \operatorname{Im}(\tau) \, |q^{1/12} \prod_{n \ge 1} (1 - q^n)^2|^2
= \frac{1}{\pi} |\Delta(\tau)|^{1/6} \operatorname{Im}(\tau)$ for
$\alpha = \Delta(\tau)^{1/12} \, dz$. Over an extension $L'$ of $k$ over which $E$ has semistable
reduction everywhere, this agrees with the theorem for $E/L'$, since at a place of semistable
reduction the valuation of the minimal discriminant is $\max(0, -v(j))$.

Silverman's list of notation prints $\Delta(\tau) = (2\pi)^{-12} q \prod_{n \ge 1} (1 - q^n)^{24}$, but
his proof takes $\Delta(\tau_v) = g_2(\tau_v)^3 - 27 g_3(\tau_v)^2$, the discriminant of the
Weierstrass equation $Y^2 = 4X^3 - g_2(\tau_v) X - g_3(\tau_v)$ of
$\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau_v)$, and it is with this value that he writes the invariant
section $\beta = \Delta(\tau)(dz)^{\otimes 12}$ on $\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)$ and
computes $\frac{i}{2} \int \alpha \wedge \bar\alpha = |\Delta(\tau)|^{1/6} \operatorname{Im}(\tau)$ for
$\alpha = \Delta(\tau)^{1/12} dz$; by Jacobi's product formula, $g_2^3 - 27 g_3^2 = (2\pi)^{12} \eta^{24}$.
Barquero-Sanchez, Cadwallader, Cannon, Genao and Masri restate the theorem with
$\Delta = (2\pi)^{12} \eta^{24}$, and it is with this $\Delta$ that the theorem agrees with Deligne's
values: for $E$ with complex multiplication by $\mathbb{Z}[(1 + \sqrt{-3})/2]$ and good reduction
everywhere over $L$, its value of $h_F(E) + \frac{1}{2} \log \pi$, at $\tau_\sigma = e^{2\pi i/3}$, is
Deligne's minimum
$h_{\mathrm{geom}}(E) = -\frac{1}{2} \log \bigl( \frac{1}{\sqrt 3} (\Gamma(1/3)/\Gamma(2/3))^3 \bigr)
\approx -0.749$.

A good expansion has pages for: the Néron model of an elliptic curve over $\mathcal{O}_L$, its existence,
and its relation to the Néron models over the local rings $\mathcal{O}_{L,\mathfrak{p}}$; the Faltings
height $h_{\mathrm{Fal}}(E/L)$ of an elliptic curve over $L$ through its Néron model, and its
comparison with the stable height (Deligne, pp. 26–27); the minimal discriminant ideal, with the
discriminant of a minimal Weierstrass equation at each place (Silverman, "Heights and elliptic
curves", pp. 254–255); good reduction of $E$ outside the finitely many places dividing the
discriminant of a Weierstrass equation with coefficients in $\mathcal{O}_L$, which with the
[semistable reduction theorem](../abelian-varieties/semistable-reduction-theorem.md) at the other
places gives a finite extension $L'/L$ over which $E$ has semistable reduction everywhere; the
valuation of the minimal discriminant at a place of semistable reduction, $0$ at a place of good
reduction and $\max(0, -v(j))$ in general, from which the good-reduction display follows from the
theorem over $L$, and Deligne's formula from the theorem over such an $L'$; the complex uniformization
$E_\sigma(\mathbb{C}) \cong \mathbb{C}/\Lambda$ by the Weierstrass $\wp$-function and the
$\mathrm{SL}_2(\mathbb{Z})$-invariance of $|\Delta(\tau)| (\operatorname{Im} \tau)^6$; and the two
halves of the proof of the theorem: the finite places, where a minimal Weierstrass equation gives a
generator of $\omega$ at $\mathfrak{p}$ and the invariant section
$\Delta \cdot (dx / (2y + a_1 x + a_3))^{\otimes 12}$ of $\omega^{\otimes 12}$ measures
$\Delta_{E/L}$, and the infinite places, where the area of a fundamental parallelogram of
$\mathbb{Z} + \mathbb{Z}\tau$ is $\operatorname{Im} \tau$.

## Depends on

- [Néron model of an abelian variety](../abelian-varieties/neron-model.md), for the functor that the
  Néron model $\mathcal{E}$ of $E$ over $\mathcal{O}_L$ represents, through which
  $h_{\mathrm{Fal}}(E/L)$ is defined, and for good reduction at a finite place $\mathfrak{p}$, over
  the local ring $\mathcal{O}_{L,\mathfrak{p}}$
- [Semistable reduction theorem for abelian varieties](../abelian-varieties/semistable-reduction-theorem.md),
  for semistable reduction at a finite place, over the local ring, in the relation with the stable
  height
- [Stable Faltings height](../abelian-varieties/stable-faltings-height/faltings-height.md), for $h_F(E)$ and
  its normalization
- [Jacobi's product formula for the discriminant of a lattice](../../NumberTheory/modular-forms-q-series/modular-forms/lattice-discriminant-eta-product.md),
  for $\Delta(\tau) = g_2(\tau)^3 - 27 g_3(\tau)^2 = (2\pi)^{12} \eta(\tau)^{24}$

## Proof depends on

- [Semistable reduction theorem for abelian varieties](../abelian-varieties/semistable-reduction-theorem.md),
  for each finite place $\mathfrak{p}$ of $L$, a finite extension of $L$ over which $E$ has semistable
  reduction at every place above $\mathfrak{p}$, and for the identity component of the Néron model
  commuting with further finite extensions once the reduction is semistable; with good reduction
  outside finitely many places (see the expansion above), the compositum of these extensions is an
  $L'/L$ over which $E$ has semistable reduction everywhere

## Sources

- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: the minimal discriminant $\Delta_{E/K}$ and
  $\Delta(\tau)$ in the list of notation, p. 254; Proposition 1.1, p. 254, with Remark 1.2 (the height
  is not the stabilized one; independence of the $\tau_v$) and the proof, pp. 254–256 (the minimal
  Weierstrass equation (2) at a finite place, with $v(\Delta_v) = v(\Delta_{E/K})$, p. 255; the
  Weierstrass equation (3), $Y_v^2 = 4X_v^3 - g_2(\tau_v) X_v - g_3(\tau_v)$, and below it
  $\Delta_v = g_2(\tau_v)^3 - 27 g_3(\tau_v)^2 = \Delta(\tau_v)$, p. 255; the archimedean contribution
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
- P. Deligne, "Preuve des conjectures de Tate et Shafarevitch [d'après G. Faltings]", Séminaire
  Bourbaki, exposé 616 (1983/84), Astérisque 121–122 (1985), 25–41,
  <http://www.numdam.org/item/SB_1983-1984__26__25_0/>: p. 26, §1.2 (b), the metric
  $\frac{1}{(2\pi)^g} \int |\alpha \wedge \bar\alpha|$ (with Faltings' $\frac{1}{2^g} |\alpha \wedge \bar\alpha|$
  noted at the foot of p. 26); p. 27, the height $h(A)$, its invariance under extension of scalars
  for semistable reduction, the geometric height $h_{\mathrm{geom}}(A) = h(A_{k'})$ and
  $h(A) \ge h_{\mathrm{geom}}(A)$ with equality if and only if the reduction is semistable;
  Exemple 1.4, p. 28, $\Delta = (c_4^3 - c_6^2)/1728$ for $(\mathbb{C}/\Lambda, dz)$; Remarque 1.5,
  pp. 28–29, the formula for $\exp([k : \mathbb{Q}] h_{\mathrm{geom}}(E))$ and the minimum
  $h_{\min} \approx -0.749$.
