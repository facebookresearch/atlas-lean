# The isomorphism problem is undecidable for word-hyperbolic semigroups

No algorithm decides whether two word-hyperbolic semigroups, given by interpreted word-hyperbolic structures, are isomorphic, although each of them has word problem solvable in polynomial time.

A semigroup $S$ is word-hyperbolic in the sense of Duncan and Gilman if there are a finite generating set $A$ and a regular language $L \subseteq A^+$ mapping onto $S$ such that the language $\{u \#_1 v \#_2 w^{\mathrm{rev}} : u, v, w \in L,\ uv = w \text{ in } S\}$ is context-free; the source requires the interpretation $A^+ \to S$ to be injective on the alphabet $A$ (Definition 3.7), so that the structure determines $S$ up to isomorphism, and an interpreted word-hyperbolic structure is such a structure (finite automaton for $L$, context-free grammar for the multiplication language) together with an assignment of generators, a map $A \to L$ sending each letter to a word of $L$ representing the same element (Definitions 3.10 and 3.12). The isomorphism problem is undecidable for word-hyperbolic semigroups: no algorithm takes two interpreted word-hyperbolic structures and decides whether the semigroups they define are isomorphic (Theorem 5.5 of the source).

The same encoding shows that no algorithm takes an interpreted word-hyperbolic structure and decides whether the semigroup is automatic (respectively asynchronously automatic, biautomatic, asynchronously biautomatic) (Theorem 5.6). By contrast, the isomorphism problem is solvable for hyperbolic groups. Theorem 7.1 of the source is printed as a polynomial-time algorithm for the uniform word problem, polynomial in the lengths of the words and the size of the grammar; the bound its proof gives (Lemma 7.2) is $O(n^{5 + 5 \log(c+1)} \log n)$ in the total length $n$ of the input words, where the constant $c$ of Lemma 6.1 depends on the structure, so the algorithm decides the word problem, for each fixed structure, in time polynomial in the lengths of the words, and the source leaves open whether an exponent independent of the structure exists (the remark after Lemma 7.2).

## Depends on

- [Multiplication-preserving maps and group homomorphisms](../group-homomorphism.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Context-free languages](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/context-free-languages.md)

## Proof depends on

- [Universality of context-free grammars reduces from the Post correspondence problem](../../../TheoryOfComputation/undecidable-problems/universality-problem-for-context-free-grammars/many-one-reducible-not-pcp-univ.md)
- [Regularity of context-free languages is undecidable](../../../TheoryOfComputation/undecidable-problems/regularity-problem-for-context-free-languages/exists-not-tm2-decidable-is-regular.md)

## Expansion

From a context-free grammar $\Gamma$ over $B$ the source builds interpreted word-hyperbolic structures for semigroups whose isomorphism type, or automaticity, records whether $L(\Gamma) = B^*$, respectively whether $L(\Gamma)$ is regular (Lemma 5.4). Both properties of context-free grammars are undecidable (Hopcroft and Ullman, quoted as Theorems 5.1 and 5.2 in the version read).

## Sources

- A. J. Cain and M. Pfeiffer, "Decision problems for word-hyperbolic semigroups", Journal of Algebra 465 (2016), 287–321, https://doi.org/10.1016/j.jalgebra.2016.07.007; read in arXiv:1303.1763v2 (Definitions 3.7, 3.10 and 3.12, Theorems 5.1, 5.2, 5.5, 5.6 and 7.1, Lemmas 5.4 and 7.2 and the remark after Lemma 7.2, of arXiv:1303.1763v2).
