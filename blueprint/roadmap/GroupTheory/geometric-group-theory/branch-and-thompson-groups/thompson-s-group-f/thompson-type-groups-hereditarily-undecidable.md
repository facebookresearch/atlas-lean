# Groups of piecewise affine permutations meeting the continuous ones in a group F(r, Λ, A) have hereditarily undecidable theory

The elementary theory of every Thompson group $F$, $T$, $V$, every Higman group $G_{n,r}$, and every group of piecewise affine permutations of an interval that meets the continuous ones in a group $F(r, \Lambda, A)$ with $\Lambda \ne \{1\}$, is hereditarily undecidable.

Let $r > 0$ be real, $\Lambda \ne \{1\}$ a subgroup of the multiplicative group of positive reals, and $A$ an additive subgroup of $\mathbb{R}$ containing $r$ and invariant under multiplication by $\Lambda$. Let $V(r, \Lambda, A)$ be the group of bijections $x\colon [0, r) \to [0, r)$ that are piecewise affine with finitely many cuts and singularities, right-continuous, with slopes in $\Lambda$, and with all cut and singular points and their images in $A$; let $F(r, \Lambda, A)$ be its subgroup of elements continuous in the usual topology. If $G$ is a subgroup of $V(r, \mathbb{R}^*_+, \mathbb{R})$ with $G \cap F(r, \mathbb{R}^*_+, \mathbb{R}) = F(r, \Lambda, A)$, then the elementary theory of $G$, in the language of groups, is hereditarily undecidable: every subtheory in the same signature is undecidable (Theorem C of the source).

The groups $F$, $T$, $V$ of Thompson are $F(1, \langle 2 \rangle, \mathbb{Z}[1/2])$, $T(1, \langle 2 \rangle, \mathbb{Z}[1/2])$, $V(1, \langle 2 \rangle, \mathbb{Z}[1/2])$, and Higman's groups are $G_{n,r} \cong V(r, \langle n \rangle, \mathbb{Z}[1/n])$, so all of them satisfy the hypothesis. For $F$, Bardakov and Tolstykh had shown that $F$ interprets the arithmetic.

## Depends on

- [Thompson's group $F$ by its standard presentation](thompson-f.md)
- [Group](../../../group-basics/group.md)
- [Complete theory of a first-order structure](../../../../Logic/first-order-logic/theory-of-structure.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Theorem A of the source shows that such a group $G$ interprets the arithmetic $(\mathbb{N}, +, \times)$ with parameters, by finding a definable subgroup isomorphic to $\mathbb{Z} \wr \mathbb{Z}$, which interprets the arithmetic. By Mostowski, Robinson and Tarski the theory of the arithmetic has a finitely axiomatized essentially undecidable subtheory, and a structure of finite signature that interprets the arithmetic with parameters has hereditarily undecidable theory. Theorem B adds that $F(r, \Lambda, A)$ with $\Lambda$ cyclic interprets the arithmetic without parameters.

## Sources

- T. Altınel and A. Muranov, "Interprétation de l'arithmétique dans certains groupes de permutations affines par morceaux d'un intervalle", Journal of the Institute of Mathematics of Jussieu 8 (2009), no. 4, 623–652, https://doi.org/10.1017/S1474748009000024; read in arXiv:0807.1079v2 (English version, "Interpretation of the arithmetic in certain groups of piecewise affine permutations of an interval") (Theorems A, B and C in the introduction, proved in the sections "Interpretations of the arithmetic" and "Undecidability" of arXiv:0807.1079v2).
