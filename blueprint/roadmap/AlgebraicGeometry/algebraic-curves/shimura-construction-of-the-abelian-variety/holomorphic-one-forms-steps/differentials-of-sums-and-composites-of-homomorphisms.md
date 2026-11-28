# Differentials of sums and composites of homomorphisms of abelian varieties

Let $B$, $B'$ and $B''$ be [abelian varieties](../../../abelian-varieties/abelian-scheme.md) over $\mathbb{C}$, with tangent spaces
$Y_B$, $Y_{B'}$, $Y_{B''}$ at the origin and spaces $D_B$, $D_{B'}$, $D_{B''}$ of holomorphic $1$-forms, and identify
$D_B$ with the dual of $Y_B$ by evaluation at the origin, as in
[holomorphic $1$-forms on a complex abelian variety are invariant](invariant-one-forms-on-a-complex-abelian-variety.md),
writing $(u, v)_B = u_0(v)$ for $u \in D_B$ and $v \in Y_B$. For a
[homomorphism](../../../abelian-varieties/homomorphisms-of-abelian-schemes.md) $\alpha \colon B \to B'$ let
$d\alpha \colon Y_B \to Y_{B'}$ be its differential at the origin and $\delta\alpha \colon D_{B'} \to D_B$ the pullback
$u \mapsto \alpha^* u$ of holomorphic $1$-forms. Then:

1. Shimura's relation (1.1) holds:

    $$(\delta\alpha\, u, v)_B = (u, d\alpha\, v)_{B'} \qquad (u \in D_{B'},\ v \in Y_B);$$

2. $d(\alpha + \alpha') = d\alpha + d\alpha'$ and $\delta(\alpha + \alpha') = \delta\alpha + \delta\alpha'$ for homomorphisms
   $\alpha, \alpha' \colon B \to B'$, and $d0 = 0$, $\delta 0 = 0$;
3. $d(\beta \circ \alpha) = d\beta \circ d\alpha$ and $\delta(\beta \circ \alpha) = \delta\alpha \circ \delta\beta$ for a second
   homomorphism $\beta \colon B' \to B''$.

## Depends on

- [Abelian scheme](../../../abelian-varieties/abelian-scheme.md), for abelian varieties over $\mathbb{C}$
- [Homomorphisms of abelian schemes and commutativity](../../../abelian-varieties/homomorphisms-of-abelian-schemes.md), for homomorphisms
  and their sums
- [Holomorphic $1$-forms on a complex abelian variety are invariant](invariant-one-forms-on-a-complex-abelian-variety.md),
  for the identification of $D_B$ with the dual of $Y_B$

## Proof depends on

- [Holomorphic $1$-forms on a complex abelian variety are invariant](invariant-one-forms-on-a-complex-abelian-variety.md),
  for the determination of a holomorphic $1$-form by its value at the origin, which carries the rules for $d$ to
  those for $\delta$ through (1.1)

## Expansion

This node is still to be broken down. A good expansion states and links:

- relation (1.1), from the definition of the pullback of a $1$-form at the point $0$ and $\alpha(0) = 0$:
  $(\alpha^* u)_0 = u_0 \circ d\alpha$;
- the chain rule $d(\beta \circ \alpha) = d\beta \circ d\alpha$ at the origin;
- the additivity $d(\alpha + \alpha') = d\alpha + d\alpha'$, from the differential at $(0, 0)$ of the group law
  $m \colon B' \times B' \to B'$, which is the addition of $Y_{B'}$, applied to
  $\alpha + \alpha' = m \circ (\alpha, \alpha')$ (Milne (1986b), p. 116, "neither surprising nor difficult", citing
  Mumford, §4, p. 42; in the language of dual numbers, Milne's *Algebraic Groups*, 10.11);
- the passage to $\delta$: by (1.1) and the perfectness of the pairings, the rules for $d$ give those for $\delta$ on the
  values at the origin, and a holomorphic $1$-form is determined by its value at the origin.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525 (the maps $d\alpha$ and $\delta\alpha$
  and (1.1)).
- J. S. Milne, "Abelian varieties", in *Arithmetic Geometry* (G. Cornell and J. H. Silverman, eds.), Springer, 1986,
  103–150, <https://www.jmilne.org/math/articles/1986b.pdf>: proof of Theorem 8.2, p. 116 (for a homomorphism $f$,
  $(df)_0 \colon T_0(A) \to T_0(B)$, and "$d(f + g)_0 = (df)_0 + (dg)_0$ (cf. [16, §4, p. 42])").
- J. S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*, Cambridge Studies in
  Advanced Mathematics 170, Cambridge University Press, 2017; author's version
  <https://www.jmilne.org/math/Books/iAG2017.pdf>, page numbers of that version: 10.11, p. 189 (the map
  $X \mapsto e^{\varepsilon X}$ from $\mathrm{Lie}(G)$ to the kernel of $G(k[\varepsilon]) \to G(k)$ is a homomorphism of
  abelian groups).
- D. Mumford, *Abelian Varieties*, Oxford University Press, 1970: §4, p. 42, as cited in Milne (1986b) above, p. 116;
  not read for this page.
