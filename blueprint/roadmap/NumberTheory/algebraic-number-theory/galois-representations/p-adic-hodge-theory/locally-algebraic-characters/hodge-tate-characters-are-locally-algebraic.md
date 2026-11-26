# Hodge–Tate characters of local Galois groups are locally algebraic

Let $L$ and $K$ be finite extensions of $\mathbb{Q}_p$ and let
$\psi \colon G_L^{\mathrm{ab}} \to K^\times$ be a continuous character. Then $\psi$ is
[locally algebraic](locally-algebraic-characters.md) if and only if $K$, with $G_L$ acting through $\psi$
by multiplication, is a [Hodge–Tate representation](../hodge-tate-representations.md) of $G_L$ as a
$\mathbb{Q}_p$-vector space of dimension $[K : \mathbb{Q}_p]$.

The result is Tate's; Serre's account covers semisimple abelian representations, and the representation
$K$ is semisimple, as one sees after extending scalars to $\overline{\mathbb{Q}}_p$.

## Depends on

- [Locally algebraic characters of local Galois groups](locally-algebraic-characters.md)
- [Hodge–Tate representations](../hodge-tate-representations.md)

## Proof depends on

- [Hodge–Tate weights of a locally algebraic character given by one embedding](hodge-tate-weights-of-a-character-given-by-one-embedding.md), for characters $\rho$ with $\rho \circ r_F$ equal to $x \mapsto \tau(x)^{-1}$ near $1$, which are Hodge–Tate; a locally algebraic $\psi$ differs, after restriction to $G_F$ for a finite Galois extension $F$ of $\mathbb{Q}_p$ containing $K$ and $L$, from a product of their powers by a character trivial near $1$ through $r_F$
- [Sen's theorem on C-admissible representations](sen-theorem-on-c-admissible-representations.md), for the characters trivial near $1$ through the local Artin map, whose image on inertia is finite, so that they are $C$-admissible, with all Hodge–Tate weights $0$; and conversely, for a Hodge–Tate character divided by such a product so that all its weights vanish, which is then $C$-admissible and has finite image on inertia
- [Local class field theory: the local Artin map](../../../../p-adic-numbers/local-class-field-theory.md), for $r_L$: it is continuous, the units act trivially on $L^{\mathrm{ur}}$, and its reciprocity isomorphisms map the units onto the inertia subgroup of each finite abelian quotient, so that a character is trivial near $1$ through $r_L$ exactly when its image on inertia is finite
- [Local class field theory: functoriality and explicit reciprocity](../../../../p-adic-numbers/local-class-field-theory-functoriality.md), for the norm functoriality of the local Artin map (its item 1), which describes $\psi|_{G_F} \circ r_F$ as $\psi \circ r_L \circ N_{F/L}$
- [Tate–Sen theorem on the Galois cohomology of C(i)](../tate-sen-theorem.md), for $C(i)^{G} = 0$ when $i \ne 0$, which makes the Hodge–Tate weights of a product the sums of the weights

## Sources

- B. Conrad, "Lifting global representations with local properties", preprint dated December 11, 2011,
  <https://math.stanford.edu/~conrad/papers/locchar.pdf>: Appendix B, p. 32: for $L$, $K$ and $\psi$ as above, "since $\psi$ is
  semisimple when viewed as a $\mathbb{Q}_p$-linear abelian representation of $G_L$ (as we see by applying
  $(\cdot) \otimes_{\mathbb{Q}_p} \overline{\mathbb{Q}}_p$), it follows from a result of Tate (see [S6, III, A6,
  Cor. 2]) that $\psi$ is locally algebraic if and only if its underlying $\mathbb{Q}_p$-linear representation is
  Hodge–Tate".
- J.-P. Serre, *Abelian l-adic representations and elliptic curves*, 2nd edition, A. K. Peters (1998),
  Chapter III, Appendix, A6, Corollary 2, the reference [S6, III, A6, Cor. 2] of Conrad's sentence.
