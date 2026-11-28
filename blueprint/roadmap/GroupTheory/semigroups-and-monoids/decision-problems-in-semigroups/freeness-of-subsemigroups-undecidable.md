# Freeness of finitely generated subsemigroups of F2 x F2 is undecidable

No algorithm decides whether a finite subset of the direct product $F_2 \times F_2$ of two free groups of rank two freely generates the subsemigroup it generates; this holds already for subsets of bounded size.

The freeness problem for a semigroup $S$ asks, given a finite set $X \subseteq S$, whether $X$ is a free basis of the subsemigroup it generates, that is, whether every element of that subsemigroup has a unique factorization as a product of elements of $X$.

**Theorem.** The freeness problem for finitely generated subsemigroups of $F_2 \times F_2$ is undecidable, and remains undecidable when the number of generators is bounded (Proposition 3.4 of the source).

The same proposition gives undecidability of freeness for finitely generated subsemigroups of the matrix monoid $\mathbb{N}^{3 \times 3}$ and of the direct product of free monoids $\{0,1\}^* \times \{0,1\}^*$, completing the original proof of Klarner, Birget and Satterfield for $3 \times 3$ matrices. Whether freeness of finitely generated subgroups of $F_2 \times F_2$ is decidable is left open in the source.

## Depends on

- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Some finite Thue system has an undecidable word problem](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-eqv-gen.md)

## Expansion

The source first proves that the symmetric Post correspondence problem is undecidable for every alphabet of size at least $2$, already in a bounded form, where an instance is symmetric if with each pair $(u, v)$ it also contains $(v, u)$ (Proposition 2.1). Floyd's proof of undecidability of the Post correspondence problem reduces the word problem of a semi-Thue system to a Post correspondence instance; starting from a finitely presented semigroup with undecidable word problem, whose relations are symmetric, the instance is almost symmetric, and adding swapped pairs with marker letters makes it symmetric without changing solvability. Symmetric instances make the encoding of Klarner, Birget and Satterfield correct: freeness becomes undecidable in $\{0,1\}^* \times \{0,1,2,3\}^*$, hence in $\{0,1\}^* \times \{0,1\}^*$ by coding four letters as two-letter blocks, and in $F_2 \times F_2$ because $\{0,1\}^*$ is a submonoid of $F_2$. A good expansion links pages for the symmetric Post correspondence problem and the encoding lemmas.

## Sources

- J.-C. Birget and A. L. Talambutsa, "The symmetric Post correspondence problem, and errata for the freeness problem for matrix semigroups", International Journal of Algebra and Computation 32 (2022), no. 6, 1261–1274, https://doi.org/10.1142/S0218196722500540; read in arXiv:2112.02408v2, whose numbering is used here (Propositions 2.1 and 3.4 of arXiv:2112.02408v2).
