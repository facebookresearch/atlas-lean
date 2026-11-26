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

- [Hodge–Tate sequence of a p-divisible group](../hodge-tate-sequence-of-p-divisible-groups.md), for the Hodge–Tate decomposition of the Tate module of a Lubin–Tate formal group, which makes the characters of the form above Hodge–Tate
- [Tate–Sen theorem on the Galois cohomology of C(i)](../tate-sen-theorem.md), for the converse: a character whose Hodge–Tate weights all vanish has finite image on inertia
- [Local class field theory: the local Artin map](../../../../p-adic-numbers/local-class-field-theory.md), for the description of a Lubin–Tate character through $r_L$

## Sources

- B. Conrad, "Lifting global representations with local properties", preprint dated December 11, 2011,
  <https://math.stanford.edu/~conrad/papers/locchar.pdf>: Appendix B, p. 32: for $L$, $K$ and $\psi$ as above, "since $\psi$ is
  semisimple when viewed as a $\mathbb{Q}_p$-linear abelian representation of $G_L$ (as we see by applying
  $(\cdot) \otimes_{\mathbb{Q}_p} \overline{\mathbb{Q}}_p$), it follows from a result of Tate (see [S6, III, A6,
  Cor. 2]) that $\psi$ is locally algebraic if and only if its underlying $\mathbb{Q}_p$-linear representation is
  Hodge–Tate".
- J.-P. Serre, *Abelian l-adic representations and elliptic curves*, 2nd edition, A. K. Peters (1998),
  Chapter III, Appendix, A6, Corollary 2, the reference [S6, III, A6, Cor. 2] of Conrad's sentence.
