# Hodge–Tate characters of local Galois groups are locally algebraic

This node is still to be broken down. Let $L$ and $K$ be finite extensions of $\mathbb{Q}_p$ and let
$\psi \colon G_L^{\mathrm{ab}} \to K^\times$ be a continuous character. Then $\psi$ is
[locally algebraic](locally-algebraic-characters.md) if and only if $K$, with $G_L$ acting through $\psi$
by multiplication, is a [Hodge–Tate representation](../hodge-tate-representations.md) of $G_L$ as a
$\mathbb{Q}_p$-vector space of dimension $[K : \mathbb{Q}_p]$.

The result is Tate's. Conrad deduces the equivalence from Serre's account after noting that the
representation $K$ is semisimple, as one sees after extending scalars to $\overline{\mathbb{Q}}_p$.

A good expansion has pages for the two descent steps from $G_F$, for a finite Galois extension $F$ of
$\mathbb{Q}_p$ containing $K$ and $L$, to $G_L$:

- for locally algebraic implies Hodge–Tate: a $C_L$-representation of $G_L$ is Hodge–Tate if and only if it is
  Hodge–Tate as a representation of $G_F$ (Brinon–Conrad, Theorem 2.4.6, p. 20);
- for Hodge–Tate implies locally algebraic: once $\psi|_{G_F}$ is locally algebraic, that is,
  $\psi \circ r_L \circ N_{F/L}$ agrees near $1$ with a homomorphism of $\mathbb{Q}_p$-tori
  $R_{F/\mathbb{Q}_p}(\mathbb{G}_m) \to R_{K/\mathbb{Q}_p}(\mathbb{G}_m)$, that homomorphism factors through the norm
  $N_{F/L} \colon R_{F/\mathbb{Q}_p}(\mathbb{G}_m) \to R_{L/\mathbb{Q}_p}(\mathbb{G}_m)$, whose kernel is a connected
  torus, and the image of the norm $N_{F/L}(F^\times)$ is open in $L^\times$, so that $\psi \circ r_L$ itself agrees near
  $1$ with a homomorphism $R_{L/\mathbb{Q}_p}(\mathbb{G}_m) \to R_{K/\mathbb{Q}_p}(\mathbb{G}_m)$.

It also needs, for both directions, that $r_L$ maps the units of $L$ onto a dense subgroup of the inertia subgroup
of $G_L^{\mathrm{ab}}$, so that a character is trivial near $1$ through $r_L$ exactly when its image on inertia is
finite.

## Depends on

- [Locally algebraic characters of local Galois groups](locally-algebraic-characters.md)
- [Hodge–Tate representations](../hodge-tate-representations.md)

## Proof depends on

Its proof uses the descent steps listed in the expansion note, and:

- [Hodge–Tate weights of a locally algebraic character given by one embedding](hodge-tate-weights-of-a-character-given-by-one-embedding.md), for characters $\rho$ with $\rho \circ r_F$ equal to $x \mapsto \tau(x)^{-1}$ near $1$, which are Hodge–Tate; a locally algebraic $\psi$ differs, after restriction to $G_F$ for a finite Galois extension $F$ of $\mathbb{Q}_p$ containing $K$ and $L$, from a product of their powers by a character trivial near $1$ through $r_F$
- [Sen's theorem on C-admissible representations](sen-theorem-on-c-admissible-representations.md), for the characters trivial near $1$ through the local Artin map, whose image on inertia is finite, so that they are $C$-admissible, with all Hodge–Tate weights $0$; and conversely, for a Hodge–Tate character divided by such a product so that all its weights vanish, which is then $C$-admissible and has finite image on inertia
- [Local class field theory: the local Artin map](../../../../p-adic-numbers/local-class-field-theory.md), for $r_L$: its continuity, the triviality of the units on $L^{\mathrm{ur}}$, and its reciprocity isomorphisms, from which the third step of the expansion note follows
- [Local class field theory: functoriality and explicit reciprocity](../../../../p-adic-numbers/local-class-field-theory-functoriality.md), for the norm functoriality of the local Artin map (its item 1), which describes $\psi|_{G_F} \circ r_F$ as $\psi \circ r_L \circ N_{F/L}$
- [Tate–Sen theorem on the Galois cohomology of C(i)](../tate-sen-theorem.md), for $C(i)^{G} = 0$ when $i \ne 0$, which makes the Hodge–Tate weights of a product the sums of the weights

## Sources

- B. Conrad, "Lifting global representations with local properties", preprint dated December 11, 2011,
  <https://math.stanford.edu/~conrad/papers/locchar.pdf>: Appendix B, p. 32: for $L$, $K$ and $\psi$ as above, "Since $\psi$ is
  semisimple when viewed as a $\mathbb{Q}_p$-linear abelian representative of $G_L$ (as we see by applying
  $(\cdot) \otimes_{\mathbb{Q}_p} \overline{\mathbb{Q}}_p$), it follows from a result of Tate (see [S6, III, A6,
  Cor. 2]) that $\psi$ is locally algebraic if and only if its underlying $\mathbb{Q}_p$-linear representation is
  Hodge–Tate".
- O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (preliminary version),
  <https://math.stanford.edu/~conrad/papers/notes.pdf>: Theorem 2.4.6, p. 20 ("for any finite extension $K'/K$
  inside of $\overline{K}$, an object $W$ in $\mathrm{Rep}_{C_K}(G_K)$ is Hodge–Tate if and only iff it is Hodge–Tate when
  viewed in $\mathrm{Rep}_{C_K}(G_{K'})$"), for the first descent step.
- J.-P. Serre, *Abelian l-adic representations and elliptic curves*, 2nd edition, A. K. Peters (1998),
  Chapter III, Appendix, A6, Corollary 2, as cited by Conrad ([S6, III, A6, Cor. 2], his reference [S6] being the
  2nd edition, A. K. Peters, 1998); not read here, so this locator is unverified.
