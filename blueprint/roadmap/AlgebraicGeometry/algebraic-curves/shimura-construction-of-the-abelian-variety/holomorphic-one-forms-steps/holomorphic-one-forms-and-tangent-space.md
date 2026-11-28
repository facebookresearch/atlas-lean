# Holomorphic $1$-forms and tangent space of a complex abelian variety

For an [abelian variety](../../../abelian-varieties/abelian-scheme.md) $B$ over $\mathbb{C}$, let $D_B$, or $D(B)$, be the complex vector
space of all holomorphic $1$-forms on $B$, and $Y_B$, or $Y(B)$, the tangent space of $B$ at the origin.
Evaluating a holomorphic $1$-form at the origin identifies $D_B$ with the dual of $Y_B$, and

$$( \ , \ )_B \colon D_B \times Y_B \to \mathbb{C}$$

denotes the resulting perfect $\mathbb{C}$-bilinear pairing.

For a [homomorphism](../../../abelian-varieties/homomorphisms-of-abelian-schemes.md) $\alpha \colon B \to B'$ of abelian varieties over
$\mathbb{C}$, let $d\alpha \colon Y_B \to Y_{B'}$ be its differential at the origin and
$\delta\alpha \colon D_{B'} \to D_B$ the pullback of holomorphic $1$-forms. They satisfy Shimura's relation (1.1):

$$(\delta\alpha\, u, v)_B = (u, d\alpha\, v)_{B'} \qquad (u \in D_{B'},\ v \in Y_B).$$

Both are additive in $\alpha$, and $\delta(\beta \circ \alpha) = \delta\alpha \circ \delta\beta$ for a second homomorphism
$\beta \colon B' \to B''$, so that $\delta$ extends $\mathbb{Q}$-linearly to $\mathrm{Hom}(B, B') \otimes \mathbb{Q}$ and
$\mathbb{C}$-linearly to $\mathrm{Hom}(B, B') \otimes \mathbb{C}$. If $\alpha$ is surjective, $\delta\alpha$ is injective.

## Depends on

- [Abelian scheme](../../../abelian-varieties/abelian-scheme.md), for abelian varieties over $\mathbb{C}$
- [Homomorphisms of abelian schemes and commutativity](../../../abelian-varieties/homomorphisms-of-abelian-schemes.md), for homomorphisms of abelian varieties

## Proof depends on

- [Holomorphic $1$-forms on a complex abelian variety are invariant](invariant-one-forms-on-a-complex-abelian-variety.md),
  for the identification of $D_B$ with the dual of $Y_B$ and the perfectness of $( \ , \ )_B$
- [Differentials of sums and composites of homomorphisms of abelian varieties](differentials-of-sums-and-composites-of-homomorphisms.md),
  for (1.1) and the behaviour of $d$ and $\delta$ under sums and composition
- [A surjective homomorphism of complex abelian varieties is surjective on tangent spaces](surjective-homomorphisms-are-surjective-on-tangent-spaces.md),
  for the injectivity of $\delta\alpha$ for surjective $\alpha$

## Proof sketch

Evaluation at the origin identifies $D_B$ with the dual of $Y_B$, which makes $( \ , \ )_B$ perfect. Relation (1.1)
comes from the definition of the pullback at the origin, and the rules for sums and composites from the group law and
the chain rule, carried from $d$ to $\delta$ by (1.1). As $\delta$ is additive with
values in complex vector spaces, it extends uniquely $\mathbb{Q}$-linearly to $\mathrm{Hom}(B, B') \otimes \mathbb{Q}$ and
$\mathbb{C}$-linearly to $\mathrm{Hom}(B, B') \otimes \mathbb{C}$, and the extensions still reverse composition. For a
surjective $\alpha$, $d\alpha$ is surjective, so by (1.1) and the perfectness of the pairings $\delta\alpha$ is injective.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, pp. 524–525 (the spaces $D_B$ and $Y_B$, the pairing $( \ , \ )_B$, the maps $d\alpha$ and
  $\delta\alpha$, and (1.1)).
