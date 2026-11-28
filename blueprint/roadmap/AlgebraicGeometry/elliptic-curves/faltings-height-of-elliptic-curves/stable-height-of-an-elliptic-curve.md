# Deligne's formula for the stable Faltings height of an elliptic curve

Let $k$ be a number field and $E$ an elliptic curve over $k$ with $j$-invariant $j \in k$. Let
$h_F(E)$ be its [stable Faltings height](../../abelian-varieties/stable-faltings-height/faltings-height.md),
and for $\tau \in \mathbb{H}$ let $\Delta(\tau) = g_2(\tau)^3 - 27 g_3(\tau)^2$ and
$j(\tau) = 1728\, g_2(\tau)^3 / \Delta(\tau)$, as in
[Silverman's formula](faltings-height-in-terms-of-discriminant-and-periods.md) and the
[complex uniformization](complex-uniformization.md). For each embedding $\iota : k \to \mathbb{C}$
choose $\tau_\iota \in \mathbb{H}$ with $j(\tau_\iota) = \iota(j)$, and for each finite place $v$ of $k$
let $\| \cdot \|_v$ be Deligne's absolute value at $v$, the one given by a maximal ideal $\mathfrak{p}$
of $\mathcal{O}_k$: $\| x \|_v = (N\mathfrak{p})^{-\operatorname{ord}_{\mathfrak{p}}(x)}$ for $x \ne 0$, where
$N\mathfrak{p} = \#(\mathcal{O}_k / \mathfrak{p})$, with no further factor $1/[k : \mathbb{Q}]$ (the degree
is on the left in item 2).

**Theorem.**

1. If $E$ has good reduction at every finite place of $k$, then

    $$h_F(E) = - \frac{1}{12 [k : \mathbb{Q}]} \sum_{\iota : k \to \mathbb{C}}
      \log \bigl( |\Delta(\tau_\iota)| \, (\operatorname{Im} \tau_\iota)^6 \bigr).$$

2. In general,

    $$[k : \mathbb{Q}] \, h_F(E) = \frac{1}{12} \sum_{v \text{ finite}} \log \max(1, \| j \|_v)
      - \frac{1}{12} \sum_{\iota : k \to \mathbb{C}} \log \bigl( |\Delta(\tau_\iota)| \, (\operatorname{Im} \tau_\iota)^6 \bigr).$$

Deligne states item 2 for the height $h_{\mathrm{geom}}(E) = h_F(E) + \frac{1}{2} \log \pi$, defined with
the metric $\frac{1}{2\pi} \int |s \wedge \bar s|$, as
$\exp([k : \mathbb{Q}] h_{\mathrm{geom}}(E)) = \prod_\iota V(\iota j)^{-1/2} \prod_{v \text{ finite}} \max(1, \| j \|_v)^{1/12}$,
where $V(j(\tau)) = V_0(\tau) = \frac{1}{2\pi} \int_{\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)} |\alpha \wedge \bar\alpha|
= 4\pi \operatorname{Im}(\tau) \, |q^{1/12} \prod_{n \ge 1} (1 - q^n)^2|^2$ for $\alpha = \Delta^{1/12} dz$
and $q = e^{2\pi i \tau}$; with $\Delta(\tau) = (2\pi)^{12} q \prod_{n \ge 1} (1 - q^n)^{24}$ this is
$\frac{1}{\pi} |\Delta(\tau)|^{1/6} \operatorname{Im}(\tau)$. For $E$ with $j = 0$ and good reduction at
every finite place of $k$, item 1 with $\tau_\iota = e^{2\pi i/3}$ gives
$h_F(E) + \frac{1}{2} \log \pi = -1.32112 \ldots + 0.57236 \ldots = -0.74875 \ldots$, the
value $-\frac{1}{2} \log \bigl( \frac{1}{\sqrt 3} (\Gamma(1/3)/\Gamma(2/3))^3 \bigr) \approx -0.749$
that Deligne gives for the minimum of $h_{\mathrm{geom}}$.

## Depends on

- [Stable Faltings height](../../abelian-varieties/stable-faltings-height/faltings-height.md), for $h_F(E)$
- [Faltings height of an elliptic curve in terms of its discriminant and periods](faltings-height-in-terms-of-discriminant-and-periods.md),
  for $\Delta(\tau)$ and its normalization
- [Complex uniformization of elliptic curves](complex-uniformization.md), for $j(\tau)$ and the
  existence of $\tau_\iota$

## Proof depends on

- [Faltings height of an elliptic curve in terms of its discriminant and periods](faltings-height-in-terms-of-discriminant-and-periods.md),
  for Silverman's formula over $k$ and over finite extensions of $k$
- [Faltings height over the field of definition and the stable height](faltings-height-and-stable-height.md),
  for $h_F(E) = h_{\mathrm{Fal}}(E/k)$ under good, hence semistable, reduction, and
  $h_F(E) = h_{\mathrm{Fal}}(E_{k'}/k')$ over an extension $k'$ with semistable reduction everywhere
- [Minimal Weierstrass models and the identity component of the Néron model](minimal-weierstrass-model-and-neron-model.md),
  item 2, for $\Delta_{E/k} = \mathcal{O}_k$ under good reduction everywhere
- [Complex uniformization of elliptic curves](complex-uniformization.md), items 3 and 4, and
  [invariance of $|\Delta(\tau)| (\operatorname{Im} \tau)^6$ under the modular group](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-group-and-congruence-subgroups/discriminant-im-pow-six-invariant.md),
  for the independence of the archimedean terms from the choice of $\tau_\iota$, so that the terms of
  the embeddings of $k'$ above $\iota$ all equal that of $\iota$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the valuation of the minimal discriminant at a place of semistable reduction: $0$ at a place of good
  reduction and $-v(j)$ at a place of multiplicative reduction, so $\max(0, -v(j))$ in both cases;
  Silverman (p. 257) notes that the denominator ideal of $j$ equals $\Delta_{E/K}$ when $E/K$ has
  everywhere semistable reduction, without proof;
- the comparison of the sum over the finite places of $k'$ with that over the finite places of $k$,
  through $\sum_{w \mid v} [k'_w : k_v] = [k' : k]$, for item 2.

## Sources

- P. Deligne, "Preuve des conjectures de Tate et de Shafarevitch [d'après G. Faltings]", Séminaire
  Bourbaki, exposé 616 (1983/84), Astérisque 121–122 (1985), 25–41,
  <http://www.numdam.org/item/SB_1983-1984__26__25_0/>: pp. 25–26, §1.1, the absolute values
  $\| \cdot \|_v$ on $k$, which satisfy the product formula, and
  $\#(L_{\mathcal{O}} / \mathcal{O} \cdot \ell) = \prod_{v \text{ fini}} \| \ell \|_v^{-1}$ for an
  $\mathcal{O}$-form $L_{\mathcal{O}}$ of a $k$-vector space of rank one and $\ell \in L_{\mathcal{O}}$;
  for the $\mathcal{O}$-form $\mathcal{O}_k$ of $k$ itself this gives
  $\| x \|_v = (N\mathfrak{p})^{-\operatorname{ord}_{\mathfrak{p}}(x)}$; Remarque 1.5, pp. 28–29, the function
  $V_0(\tau)$, its invariance under $\mathrm{SL}(2, \mathbb{Z})$, the function $V(j)$, the formula for
  $H_{\mathrm{geom}}(E) = \exp([k : \mathbb{Q}] h_{\mathrm{geom}}(E))$, and the minimum
  $h_{\min} = -\frac{1}{2} \log \bigl( \frac{1}{\sqrt 3} (\Gamma(1/3)/\Gamma(2/3))^3 \bigr) = -0.749$,
  which Deligne derives from D. Masser's Lemma 3.2 (Lecture Notes in Mathematics 437) and the
  Chowla–Selberg formula (J. Crelle 227 (1967), 86–110), as cited by Deligne.
- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: p. 257, $(j_E) = \mathfrak{A} \mathfrak{D}^{-1}$
  with $\mathfrak{A}$, $\mathfrak{D}$ coprime integral ideals, and $\mathfrak{D} = \Delta_{E/K}$ when
  $E/K$ has everywhere semistable reduction, $\mathfrak{D} \mid \Delta_{E/K}$ in all cases.
