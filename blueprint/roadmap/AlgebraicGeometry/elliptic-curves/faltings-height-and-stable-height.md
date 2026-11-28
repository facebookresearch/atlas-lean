# Faltings height over the field of definition and the stable height

Let $L$ be a number field with ring of integers $\mathcal{O}_L$, let $E$ be an elliptic curve over $L$,
let $h_{\mathrm{Fal}}(E/L)$ be its
[Faltings height over $L$](faltings-height-over-the-field-of-definition.md), computed with the Néron
model of $E$ over $\mathcal{O}_L$, and let $h_F(E)$ be its
[stable Faltings height](../abelian-varieties/stable-faltings-height/faltings-height.md). Say that $E$ has
semistable reduction at a maximal ideal $\mathfrak{p}$ of $\mathcal{O}_L$ if it has
[semistable reduction](../abelian-varieties/semistable-reduction-theorem.md) over the local ring
$\mathcal{O}_{L,\mathfrak{p}}$, and semistable reduction everywhere if it does at every $\mathfrak{p}$.

**Theorem** (Deligne, p. 27, for abelian varieties; here in dimension one).

1. For every finite extension $L'/L$, $h_{\mathrm{Fal}}(E_{L'}/L') \le h_{\mathrm{Fal}}(E/L)$, with
   equality if $E$ has semistable reduction everywhere over $L$.
2. There are finite extensions $L'/L$ over which $E$ has semistable reduction everywhere, and for
   each of them $h_F(E) = h_{\mathrm{Fal}}(E_{L'}/L')$.
3. $h_{\mathrm{Fal}}(E/L) \ge h_F(E)$, with equality if and only if $E$ has semistable reduction
   everywhere over $L$.

Deligne states these facts for the height defined with the metric
$\frac{1}{(2\pi)^g} \int |\alpha \wedge \bar\alpha|$, which differs from $h_{\mathrm{Fal}}$ and $h_F$ by
the same constant $\frac{g}{2} \log \pi$.

## Depends on

- [Faltings height of an elliptic curve over its field of definition](faltings-height-over-the-field-of-definition.md),
  for $h_{\mathrm{Fal}}(E/L)$
- [Stable Faltings height](../abelian-varieties/stable-faltings-height/faltings-height.md), for $h_F(E)$
- [Semistable reduction theorem for abelian varieties](../abelian-varieties/semistable-reduction-theorem.md),
  for semistable reduction over a discrete valuation ring

## Proof depends on

- [Néron model of an abelian variety](../abelian-varieties/neron-model.md), for the Néron mapping
  property, which gives the morphism from the base change of the Néron model over $\mathcal{O}_L$ to
  the Néron model over $\mathcal{O}_{L'}$
- [Néron model of an abelian variety over the ring of integers of a number field](../abelian-varieties/stable-faltings-height/neron-model-over-a-ring-of-integers.md),
  for good reduction outside finitely many maximal ideals and the localization of the Néron model
- [Semistable reduction theorem for abelian varieties](../abelian-varieties/semistable-reduction-theorem.md),
  for semistable reduction after a finite extension at each of the finitely many remaining maximal
  ideals, and for the identity component of a semistable Néron model commuting with finite
  extensions
- [The stable Faltings height is invariant under finite extension](../abelian-varieties/stable-faltings-height/faltings-height-field-base-change.md),
  for the independence of $h_F(E)$ from the extension

## Expansion

This node is still to be broken down. A good expansion states and links:

- the pullback map $\omega_{\mathcal{E}'} \to \omega_{\mathcal{E}} \otimes_{\mathcal{O}_L} \mathcal{O}_{L'}$
  induced by the morphism of Néron models, an isomorphism on generic fibres, and the comparison of
  the arithmetic degrees of two nested lattices with the same metrics (Deligne, p. 27), for item 1;
- the equality of $\varepsilon^* \Omega^1$ for the Néron model and for its identity component, and
  the identification of the identity component of a semistable Néron model over $\mathcal{O}_{L'}$
  with the semi-abelian model of the stable height, for item 2;
- the compositum of the local extensions given by the semistable reduction theorem at the finitely
  many places of bad reduction, made global, for the existence in item 2;
- the converse in item 3: if the pullback map is an isomorphism at the places above $\mathfrak{p}$ for
  an extension over which $E$ becomes semistable, then $E$ has semistable reduction at $\mathfrak{p}$
  (stated by Deligne, p. 27, without proof).

## Sources

- P. Deligne, "Preuve des conjectures de Tate et de Shafarevitch [d'après G. Faltings]", Séminaire
  Bourbaki, exposé 616 (1983/84), Astérisque 121–122 (1985), 25–41,
  <http://www.numdam.org/item/SB_1983-1984__26__25_0/>: §1.2, p. 26, the metric
  $\frac{1}{(2\pi)^g} \int |\alpha \wedge \bar\alpha|$ and Faltings' $\frac{1}{2^g} |\alpha \wedge \bar\alpha|$;
  p. 27, Remarque: semi-abelian group schemes, semistable reduction through the connected Néron model
  $A^0_{\mathcal{O}}$, the commutation of $A^0_{\mathcal{O}}$ and of
  $\omega(A)_{\mathcal{O}} = \omega(A^0_{\mathcal{O}})$ with extension of scalars when the reduction is
  semistable, the invariance of $h(A)$ under extension of scalars in that case, the geometric height
  $h_{\mathrm{geom}}(A) = h(A_{k'})$ for an extension $k'$ over which $A$ acquires semistable
  reduction, and, since $(A_{\mathcal{O}})_{\mathcal{O}'}$ maps to $(A_{k'})_{\mathcal{O}'}$, the
  inequality $h(A) \ge h_{\mathrm{geom}}(A)$, with equality if and only if the reduction is
  semistable.
- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: p. 254, Remark 1.2 (1), the height $h(E/K)$ is not
  the stabilized height obtained over an extension over which $E$ has everywhere semistable reduction.
