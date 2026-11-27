# Similarity of bounded unital homomorphisms to star homomorphisms

Let $A$ be a unital complex $C^*$-algebra and $H$ a complete complex Hilbert space. For every continuous complex-linear unital algebra homomorphism $\pi:A\to\mathcal B(H)$, there is a bounded invertible $S\in\mathcal B(H)$ such that $a\mapsto S\pi(a)S^{-1}$ preserves adjoints: $S\pi(a^*)S^{-1}=(S\pi(a)S^{-1})^*$ for every $a$. There is no separability assumption and the algebra and Hilbert-space universes are independent.

## Depends on
Bounded unital complex algebra homomorphisms, units of the bounded operator algebra, and star preservation of the conjugated map.

## Proof depends on

- [Universal amplified commutator estimate](../norm-estimates-stability-and-cohomology/uniform-matrix-commutator-bound.md).

A finite-cyclic reduction from uniform inner-derivation control to a completely bounded homomorphism, and the Paulsen similarity theorem turning complete boundedness into a star representation.

## Expansion

Prove the matrix bounds on finite cyclic orbit subspaces with a constant independent of matrix size, then pass from complete boundedness to a bounded invertible similarity. Keep the source algebra and Hilbert spaces in independent universes and do not assume that the input representation preserves adjoints.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KadisonSimilarity.lean#L114-L117) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/288.md).
