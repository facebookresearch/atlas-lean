# A surjective homomorphism of complex abelian varieties is surjective on tangent spaces

Let $\alpha \colon B \to B'$ be a surjective [homomorphism](../../../abelian-varieties/homomorphisms-of-abelian-schemes.md) of
[abelian varieties](../../../abelian-varieties/abelian-scheme.md) over $\mathbb{C}$, with tangent spaces $Y_B$, $Y_{B'}$ at the origin and
spaces $D_B$, $D_{B'}$ of holomorphic $1$-forms. Then the differential $d\alpha \colon Y_B \to Y_{B'}$ at the origin is
surjective. Hence, by Shimura's relation (1.1) and the perfectness of the pairings of
[differentials of sums and composites](differentials-of-sums-and-composites-of-homomorphisms.md), the pullback
$\delta\alpha \colon D_{B'} \to D_B$ is injective.

## Depends on

- [Abelian scheme](../../../abelian-varieties/abelian-scheme.md), for abelian varieties over $\mathbb{C}$
- [Homomorphisms of abelian schemes and commutativity](../../../abelian-varieties/homomorphisms-of-abelian-schemes.md), for homomorphisms
- [Differentials of sums and composites of homomorphisms of abelian varieties](differentials-of-sums-and-composites-of-homomorphisms.md),
  for $d\alpha$, $\delta\alpha$ and (1.1)

## Proof depends on

- [Differentials of sums and composites of homomorphisms of abelian varieties](differentials-of-sums-and-composites-of-homomorphisms.md),
  for (1.1), which makes $\delta\alpha$ injective once $d\alpha$ is surjective
- [Holomorphic $1$-forms on a complex abelian variety are invariant](invariant-one-forms-on-a-complex-abelian-variety.md),
  for the perfectness of the pairings

## Expansion

This node is still to be broken down. A good expansion states and links:

- Cartier's theorem in the form that every algebraic group over a field of characteristic zero is smooth (Milne,
  *Algebraic Groups*, Corollary 8.39), applied to the kernel of $\alpha$;
- the criterion that a surjective homomorphism of group varieties has surjective differential at the identity if and
  only if its kernel is smooth (Milne, *Algebraic Groups*, Proposition 1.63, whose proof compares
  $\dim B = \dim \mathrm{Ker}(\alpha) + \dim B'$ with the exact sequence of tangent spaces of the kernel, $B$ and $B'$);
- the identification of the tangent space of the variety $B$ at $0$ with the holomorphic tangent space of $B(\mathbb{C})$,
  for which $d\alpha$ is the differential of the holomorphic map $\alpha$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525 (the maps $d\alpha$ and $\delta\alpha$,
  (1.1), and the quotient map $\nu$ of a quotient, to which this page is applied in (1.2)).
- J. S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*, Cambridge Studies in
  Advanced Mathematics 170, Cambridge University Press, 2017; author's version
  <https://www.jmilne.org/math/Books/iAG2017.pdf>, page numbers of that version: Proposition 1.63 and its proof,
  pp. 25–26 (for a surjective homomorphism $\varphi$ of group varieties, $(d\varphi)_e$ is surjective if and only if the
  kernel of $\varphi$ is smooth); Corollary 8.39, p. 158 ("Every algebraic group over a field of characteristic zero is
  smooth").
