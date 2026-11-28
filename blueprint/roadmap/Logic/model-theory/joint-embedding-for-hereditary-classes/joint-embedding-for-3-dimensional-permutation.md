# Joint embedding for 3-dimensional permutation classes is undecidable

No algorithm decides, given finitely many forbidden 3-dimensional permutations, whether the class of 3-dimensional permutations avoiding them has the joint embedding property; the same holds in every dimension $n \geq 3$. For ordinary permutations ($n = 2$) the question, Ruškuc's atomicity problem, is left open by the source.

**Definition.** An *$n$-dimensional permutation* is a finite structure $(A, <_1, \dots, <_n)$ with $n$ linear orders on the same set $A$; ordinary permutations are the case $n = 2$, and embeddings are injective maps preserving all $n$ orders. An *$n$-dimensional permutation class* is a class of finite $n$-dimensional permutations closed under isomorphism and substructures; it is *finitely constrained* if it consists of all structures that embed none of finitely many given forbidden $n$-dimensional permutations.

**Theorem (Braunfeld).** There is no algorithm that, given a finite set of forbidden 3-dimensional permutations, decides whether the corresponding 3-dimensional permutation class has the [joint embedding property](joint-embedding-property.md).

**Corollary.** For every $n \geq 3$, the joint embedding property is undecidable for $n$-dimensional permutation classes given by finitely many forbidden $n$-dimensional permutations.

For hereditary classes of permutations, the joint embedding property is the same as atomicity, not being a union of two proper subclasses.

## Depends on

- [Joint embedding property](joint-embedding-property.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces from string tiling problems, a variant of the tiling problem with two tile types and constraints on tiles at bounded horizontal distance, into which ordinary tiling problems encode. From a string tiling problem $\mathcal{T}$ one builds a finitely constrained 3-dimensional permutation class $\mathcal{Q}_\mathcal{T}$ and two countable structures $A^*$, encoding a grid, and $B^*$, encoding tiles, whose finite substructures all belong to the class; by compactness, the JEP for the finite members of a hereditary class is equivalent to the JEP for its countable members (Section 2 of the source), so the source works with such countable canonical models, $A^*$ built on an infinite path (Section 3.2). Any joint embedding of $A^*$ and $B^*$ encodes a solution, and a solution yields the joint embedding property for the whole class; so $\mathcal{T}$ has a solution iff $\mathcal{Q}_\mathcal{T}$ has the JEP. For $n > 3$, expand each constraint to $n$ orders: a 3-dimensional class has the JEP iff its expansion does, since joint embeddings transfer through reducts and expansions.

## Sources

- S. Braunfeld, "The undecidability of joint embedding for 3-dimensional permutation classes", *Discrete Mathematics & Theoretical Computer Science* 22(2), Permutation Patterns 2019, 2021, paper 6165, doi:10.46298/dmtcs.6165; read as arXiv:2002.11494v4, <https://arxiv.org/abs/2002.11494v4>: Theorem 1.3 (statement), Theorem 6.6 and Corollary 6.7 of arXiv:2002.11494v4 with their proofs, and Section 2 (string tiling problems).
