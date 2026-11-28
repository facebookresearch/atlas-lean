# Holomorphic $1$-forms on a complex abelian variety are invariant

Let $B$ be an [abelian variety](../../../abelian-varieties/abelian-scheme.md) of dimension $g$ over $\mathbb{C}$, let $Y_B$ be its tangent
space at the origin, the tangent space of the nonsingular variety $B$ at $0$, which is also the holomorphic tangent
space of the complex manifold $B(\mathbb{C})$ at $0$, and let $D_B$ be the complex vector space of holomorphic
$1$-forms on $B(\mathbb{C})$. Then every $\omega \in D_B$ is invariant under translations: $t_b^* \omega = \omega$ for
every $b \in B(\mathbb{C})$, where $t_b(x) = x + b$. Consequently a holomorphic $1$-form is determined by its value
$\omega_0$ at the origin, and evaluation at the origin,

$$D_B \to \mathrm{Hom}_{\mathbb{C}}(Y_B, \mathbb{C}), \qquad \omega \mapsto \omega_0,$$

is an isomorphism of complex vector spaces. In particular $\dim_{\mathbb{C}} D_B = \dim_{\mathbb{C}} Y_B = g$, and the
pairing $D_B \times Y_B \to \mathbb{C}$, $(\omega, v) \mapsto \omega_0(v)$, is perfect.

## Depends on

- [Abelian scheme](../../../abelian-varieties/abelian-scheme.md), for abelian varieties over $\mathbb{C}$ and their dimension

## Proof depends on

- [Abelian scheme](../../../abelian-varieties/abelian-scheme.md), for the group law of $B$, which the translations $t_b$ come from

## Expansion

This node is still to be broken down. A good expansion states and links:

- the exponential map $\exp \colon Y_B \to B(\mathbb{C})$, a surjective homomorphism of complex Lie groups whose kernel
  $L$ is a full lattice in $Y_B$ and whose differential at $0$ is the identity, so that $B(\mathbb{C}) \cong Y_B / L$
  (Milne's course notes, Proposition I.2.1);
- the description of the holomorphic $1$-forms on $Y_B / L$: in linear coordinates $z_1, \dots, z_g$ on $Y_B$ a
  holomorphic $1$-form is $\sum_i f_i \, dz_i$ with $L$-periodic holomorphic $f_i$, which are constant because a
  holomorphic function on a compact connected complex manifold is constant; so the holomorphic $1$-forms are the
  translation-invariant forms $\sum_i c_i \, dz_i$;
- the identification of the tangent space of the nonsingular variety $B$ at $0$ with the holomorphic tangent space of
  $B(\mathbb{C})$ at $0$;
- or, algebraically, the invariance of the regular $1$-forms on $B$, which makes the canonical map from them to the dual
  of the tangent space at $0$ an isomorphism (stated for a Jacobian variety $J$ by Milne (1986c), p. 172, "As for any
  group variety"), together with the comparison of regular and holomorphic $1$-forms on $B$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, pp. 524–525 (the spaces $D_B$ and $Y_B$, with
  "Then $D_B$ is dual to $Y_B$", and the pairing $( \ , \ )_B$).
- J. S. Milne, "Jacobian varieties", in *Arithmetic Geometry* (G. Cornell and J. H. Silverman, eds.), Springer, 1986,
  167–212, <https://www.jmilne.org/math/articles/1986c.pdf>: proof of Proposition 2.2, p. 172 (the canonical map
  $h_J$ from $\Gamma(J, \Omega^1_J)$ to the dual of $T_0(J)$ is an isomorphism, stated "As for any group variety" with a
  reference to Shafarevich, his [18, III, 5.2]).
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008), <https://www.jmilne.org/math/CourseNotes/AV.pdf>:
  Chapter I, Proposition 2.1, pp. 10–11 (the exponential map of $A(\mathbb{C})$, surjective with kernel a full lattice,
  with differential at $0$ the identity).
- I. R. Shafarevich, *Basic Algebraic Geometry*, Springer, 1974: III, 5.2, as cited in Milne (1986c) above, p. 172; not
  read for this page.
