# Holomorphic $1$-forms of an abelian variety over $\mathbb{Q}$ and those defined over $\mathbb{Q}$

Let $A'$ be an [abelian variety](../../../abelian-varieties/abelian-scheme.md) over $\mathbb{Q}$, let $D_{A'}$ be the complex vector space of
holomorphic $1$-forms on $A'(\mathbb{C})$, and let $D_{A', \mathbb{Q}} = \Gamma(A', \Omega^1_{A'/\mathbb{Q}})$ be the
$\mathbb{Q}$-vector space of regular $1$-forms on $A'$ defined over $\mathbb{Q}$. Each element of $D_{A', \mathbb{Q}}$ defines
a holomorphic $1$-form on $A'(\mathbb{C})$, and the resulting $\mathbb{C}$-linear map

$$\mathbb{C} \otimes_{\mathbb{Q}} D_{A', \mathbb{Q}} \to D_{A'}$$

is an isomorphism. In particular $\dim_{\mathbb{Q}} D_{A', \mathbb{Q}} = \dim A'$. For every
[endomorphism](../../../abelian-varieties/homomorphisms-of-abelian-schemes.md) $\beta$ of $A'$ defined over $\mathbb{Q}$, the pullback
$\beta^* \colon D_{A'} \to D_{A'}$ of holomorphic $1$-forms maps $D_{A', \mathbb{Q}}$ into itself, where it is the
pullback of regular $1$-forms; so under the isomorphism $\beta^*$ is $1 \otimes (\beta^* |_{D_{A', \mathbb{Q}}})$.

## Depends on

- [Abelian scheme](../../../abelian-varieties/abelian-scheme.md), for abelian varieties over $\mathbb{Q}$
- [Homomorphisms of abelian schemes and commutativity](../../../abelian-varieties/homomorphisms-of-abelian-schemes.md), for endomorphisms
  defined over $\mathbb{Q}$

## Proof depends on

- [Holomorphic $1$-forms on a complex abelian variety are invariant](../holomorphic-one-forms-steps/invariant-one-forms-on-a-complex-abelian-variety.md),
  for the isomorphism of $D_{A'}$ with the dual of the tangent space of $A'_{\mathbb{C}}$ at the origin
- [Differentials of sums and composites of homomorphisms of abelian varieties](../holomorphic-one-forms-steps/differentials-of-sums-and-composites-of-homomorphisms.md),
  for relation (1.1), which describes the pullback by its effect at the origin

## Expansion

This node is still to be broken down. A good expansion states and links:

- the invariance of the regular $1$-forms on the abelian variety $A'$ over $\mathbb{Q}$, so that evaluation at the origin
  is an isomorphism of $D_{A', \mathbb{Q}}$ onto the dual of the tangent space $T_0(A')$ of $A'$ at the origin (stated for a
  Jacobian variety over any field by Milne (1986c), p. 172, "As for any group variety");
- the base change of the tangent space at the rational point $0$: $T_0(A'_{\mathbb{C}}) = \mathbb{C} \otimes_{\mathbb{Q}} T_0(A')$;
- the compatibility of the two evaluations at the origin, for regular and for holomorphic $1$-forms, which with the
  invariance of the holomorphic $1$-forms on $A'(\mathbb{C})$ gives the isomorphism;
- for $\beta$ defined over $\mathbb{Q}$, the pullback of a regular $1$-form defined over $\mathbb{Q}$ is again one, and by
  relation (1.1) its value at the origin is the composite of the value of the form with $d\beta$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 527, proof of Theorem 1 ("Then the elements of
  $\theta'(K) \cap \mathrm{End}(A')$ are rational over $\mathbf{Q}$, hence the representation of $K$ on $D_{A'}$ via
  $\theta'$ is a multiple of a regular representation of $K$ over $\mathbf{Q}$", the step that rests on this page).
- J. S. Milne, "Jacobian varieties", in *Arithmetic Geometry* (G. Cornell and J. H. Silverman, eds.), Springer, 1986,
  167–212, <https://www.jmilne.org/math/articles/1986c.pdf>: proof of Proposition 2.2, p. 172 (the canonical map $h_J$
  from $\Gamma(J, \Omega^1_J)$ to the dual of $T_0(J)$ is an isomorphism, for the Jacobian $J$ of a curve over a field
  $k$, stated "As for any group variety" with a reference to Shafarevich, his [18, III, 5.2]).
- I. R. Shafarevich, *Basic Algebraic Geometry*, Springer, 1974: III, 5.2, as cited in Milne (1986c) above, p. 172; not
  read for this page.
