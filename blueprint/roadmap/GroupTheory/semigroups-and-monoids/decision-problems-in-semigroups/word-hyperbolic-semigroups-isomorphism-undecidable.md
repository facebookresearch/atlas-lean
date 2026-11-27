# The isomorphism problem is undecidable for word-hyperbolic semigroups

No algorithm decides whether two word-hyperbolic semigroups, given by interpreted word-hyperbolic structures, are isomorphic; the uniform word problem for these semigroups is solvable in polynomial time.

A semigroup $S$ is word-hyperbolic in the sense of Duncan and Gilman if there are a finite generating set $A$ and a regular language $L \subseteq A^+$ mapping onto $S$ such that the language $\{u \#_1 v \#_2 w^{\mathrm{rev}} : u, v, w \in L,\ uv = w \text{ in } S\}$ is context-free; an interpreted word-hyperbolic structure is the source's slight strengthening of this data (finite automaton for $L$, context-free grammar for the multiplication language, and an interpretation of the generators), needed so that the structure determines $S$ up to isomorphism. The isomorphism problem is undecidable for word-hyperbolic semigroups: no algorithm takes two interpreted word-hyperbolic structures and decides whether the semigroups they define are isomorphic (Theorem 5.5 of the source).

The same encoding shows that no algorithm takes an interpreted word-hyperbolic structure and decides whether the semigroup is automatic (respectively asynchronously automatic, biautomatic, asynchronously biautomatic) (Theorem 5.6). By contrast, the isomorphism problem is solvable for hyperbolic groups, and the source proves the uniform word problem for word-hyperbolic semigroups solvable in polynomial time (Theorem 7.1).

## Depends on

- [Multiplication-preserving maps and group homomorphisms](../group-homomorphism.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Universality of context-free grammars reduces from the Post correspondence problem](../../../TheoryOfComputation/undecidable-problems/universality-problem-for-context-free-grammars/many-one-reducible-not-pcp-univ.md)
- [Regularity of context-free languages is undecidable](../../../TheoryOfComputation/undecidable-problems/regularity-problem-for-context-free-languages/exists-not-tm2-decidable-is-regular.md)

## Expansion

From a context-free grammar $\Gamma$ over $B$ the source builds interpreted word-hyperbolic structures for semigroups whose isomorphism type, or automaticity, records whether $L(\Gamma) = B^*$, respectively whether $L(\Gamma)$ is regular (Lemma 5.4). Both properties of context-free grammars are undecidable (Hopcroft and Ullman, quoted as Theorems 5.1 and 5.2 in the version read).

## Sources

- A. J. Cain and M. Pfeiffer, "Decision problems for word-hyperbolic semigroups", Journal of Algebra 465 (2016), 287–321, https://doi.org/10.1016/j.jalgebra.2016.07.007; read in arXiv:1303.1763v2 (Theorems 5.1, 5.2, 5.5, 5.6 and 7.1 and Lemma 5.4 of arXiv:1303.1763v2).
