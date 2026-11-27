# Hodge–Tate weights of a locally algebraic character given by one embedding

This node is still to be broken down. Let $F$ be a finite Galois extension of $\mathbb{Q}_p$, $C_F$ the completion of
an algebraic closure of $F$, and $\tau \in \operatorname{Gal}(F/\mathbb{Q}_p)$. Use the arithmetic normalization of
the [local Artin map](../../../../p-adic-numbers/local-class-field-theory.md) $r_F$. Let
$\rho \colon G_F^{\mathrm{ab}} \to F^\times$ be a continuous character such that $\rho(r_F(x)) = \tau(x)^{-1}$ for all
$x$ in a neighbourhood of $1$ in $F^\times$; it is [locally algebraic](locally-algebraic-characters.md). Then $F$,
with $G_F$ acting through $\rho$, is a [Hodge–Tate](../hodge-tate-representations.md) $\mathbb{Q}_p$-linear
representation. The semilinear representation $C_F \otimes_{\mathbb{Q}_p} F$ decomposes into $G_F$-stable
$C_F$-lines indexed by $g \in \operatorname{Gal}(F/\mathbb{Q}_p)$, the line on which $F$ acts through $g$, and the
line of $g$ is $C_F(0)$ for $g \ne \tau^{-1}$ and $C_F(1)$ for $g = \tau^{-1}$: its Hodge–Tate weight, in the
convention in which the cyclotomic character has weight $1$, is $1$ for $g = \tau^{-1}$ and $0$ otherwise.

For $F = \mathbb{Q}_p$ there is one line, and it has weight $1$.

A good expansion has pages for: Lubin–Tate formal groups $G$ over the ring of integers $\mathcal{O}_F$ of $F$, with
the action of $\mathcal{O}_F$ by endomorphisms, the Galois action on their torsion points and its description
through $r_F$ on the units; Tate's $G_F$-equivariant Hodge–Tate sequence for a $p$-divisible group over
$\mathcal{O}_F$, functorial in the $p$-divisible group, applied to a Lubin–Tate group: $\mathcal{O}_F$ acts on
$\operatorname{Lie} G \otimes C_F(1)$ through the inclusion $\mathcal{O}_F \subset C_F$, which identifies this
weight-$1$ part with the line indexed by the identity, while the lines indexed by $g \ne \mathrm{id}$ map
isomorphically onto the quotient of weight $0$; and the passage from the Lubin–Tate character to the characters
$\rho$ above, by characters of finite order on inertia and by conjugation by $\tau$, which moves the weight-$1$ line
to $g = \tau^{-1}$.

## Depends on

- [Locally algebraic characters of local Galois groups](locally-algebraic-characters.md)
- [Hodge–Tate representations](../hodge-tate-representations.md), for the weights
- [Local class field theory: the local Artin map](../../../../p-adic-numbers/local-class-field-theory.md), for $r_F$ and its arithmetic normalization
- [Cyclotomic character and Tate twists](../../cyclotomic-character-and-tate-twists.md), for $C_F(1)$

## Proof depends on

- [Hodge–Tate sequence of a p-divisible group](../hodge-tate-sequence-of-p-divisible-groups.md), for the exactness of the Hodge–Tate sequence of the Lubin–Tate group after base change to the ring of integers of $C_F$, without Galois action
- [Tate–Sen theorem on the Galois cohomology of C(i)](../tate-sen-theorem.md), for $C_F(i)^{G_F} = 0$ when $i \ne 0$, which makes the weights well defined

Its proof also uses the inputs listed in the expansion note, in particular Tate's $G_F$-equivariant and
$\mathcal{O}_F$-equivariant Hodge–Tate sequence.

## Sources

- B. Conrad, "Lifting global representations with local properties", preprint dated December 11, 2011,
  <https://math.stanford.edu/~conrad/papers/locchar.pdf>: Appendix B, proof of Proposition B.3, p. 34: for a locally algebraic
  $\rho \colon G_{F'}^{\mathrm{ab}} \to F'^\times$ with $F'/\mathbb{Q}_p$ finite Galois such that $\rho \circ r_{F'}$ agrees
  near $1$ with $x \mapsto \tau(x)^{-1}$ for $\tau \in \operatorname{Gal}(F'/\mathbb{Q}_p)$, "the semilinear extension
  $\rho \otimes_{\mathbb{Q}_p} C_{F'}$ canonically decomposes into a direct product of lines indexed by
  $g \in \operatorname{Gal}(F'/\mathbb{Q}_p)$, and by [S6, III, A.5, Thm. 2] (especially Lemma 2 in its proof) the $g$th
  line has Hodge–Tate weight $0$ except for $g = \tau^{-1}$, which has weight $1$ (due to our arithmetic
  normalization of the local Artin map)"; the arithmetic normalization is fixed on p. 32.
- J.-P. Serre, *Abelian l-adic representations and elliptic curves*, Advanced Book Classics, Addison-Wesley
  (1989), a reprint of the 1968 edition: Chapter III, Appendix, for a ground field $K$ and a finite extension $E$ of
  $\mathbb{Q}_p$ such that $K$ contains all $\mathbb{Q}_p$-conjugates of $E$ (A3, p. III-38): A4, pp. III-40–42 (the
  character $\chi_E$; Proposition 4, the Galois action on the Tate module of the Lubin–Tate group of $E$ is given by
  $\chi_E$; its Corollary; and the Remark that for $K$ locally compact the restriction of $\chi_E$ to the inertia
  subgroup $U_K$ is $x \mapsto N_{K/E}(x^{-1})$); A5, pp. III-42–47 (Lemma 1, the decomposition of $C \otimes_{\mathbb{Q}_p} V$
  into the lines $W_\sigma$ on which $E$ acts through $\sigma$, with $W_\sigma \cong C(\sigma \circ \rho)$; Theorem 2, p. III-44:
  $\rho$ coincides on an open subgroup of inertia with $\prod_\sigma \sigma^{-1} \circ \chi_{\sigma E}^{n_\sigma}$ exactly when each
  $W_\sigma$ is isomorphic to $C(\chi^{n_\sigma})$; and Lemma 2 with its proof, pp. III-45–46, which applies Tate's
  decomposition to the Lubin–Tate group and uses that it commutes with the action of $E$, which acts on the tangent
  space through the inclusion, so that the line of the inclusion is the part of weight $1$). The page's statement is
  the case $K = E = F$ of Theorem 2, with $n_\sigma = 1$ for $\sigma = \tau^{-1}$ and $n_\sigma = 0$ otherwise. Serre's
  reciprocity map is that of Cassels–Fröhlich, Chapter VI, §2 (Chapter III, §1.1, p. III-2), under which the
  cyclotomic character is $x \mapsto x^{-1}$ near $1$ (Example 1, p. III-2), as under the arithmetic normalization.
- J. Tate, "p-divisible groups", in *Proceedings of a Conference on Local Fields* (Driebergen, 1966), Springer
  (1967), 158–183: §4, Theorem 3, p. 179, and Corollary 2, p. 180 (for a $p$-divisible group $G$ over a complete
  discrete valuation ring of mixed characteristic with perfect residue field, a canonical isomorphism of Galois
  modules between $\operatorname{Hom}(T(G), C)$ and the direct sum of the tangent space of the dual group tensored with $C$
  and the cotangent space of $G$ tensored with $\operatorname{Hom}(H, C)$, where $H$ is the Tate module of the roots of unity),
  the decomposition Serre applies to the Lubin–Tate group.
