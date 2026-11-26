# Exhaustive generation and stable generators with breadth

(i) **Exhaustive generation.** Call a generator exhaustive for $K$ if, beyond some finite number of mistakes, the set of strings it outputs, together with the samples, is all of $K$. There are collections, already with two languages, that are generatable in the limit but admit no exhaustive generator, so a trade-off between validity and breadth is inherent in generation in the limit; the collections admitting exhaustive generation are characterized exactly by a combinatorial condition.

(ii) **Stable generators.** A generating algorithm is stable if, on every enumeration, its generator eventually stops changing. For many notions of approximate breadth, generation with breadth by stable algorithms is impossible for every collection that is not identifiable in the limit, unconditionally (without assuming decidability of the membership oracle problem), whereas unstable algorithms can achieve approximate breadth for some such collections; in general it is also impossible to train generators that achieve lower hallucination rate or higher likelihood on the target than on competing languages.

## Proof sketch

For (i), choose two nested languages $L_1 \supsetneq L_2$ with infinite difference: an exhaustive generator for $L_1$ must keep producing elements of $L_1 \setminus L_2$, which are invalid when the target is $L_2$, and an adversary alternates between the two enumerations to force infinitely many errors. For (ii), a stable generator with breadth determines, in the limit, a fixed support equal to the target minus finitely many strings, from which an identifier can be read off without solving the membership problem, because stability makes the generator a finite object that changes only finitely often.

## Depends on

- [Consistent generation with breadth requires identifiability](breadth-requires-identifiability.md)
- [Every countable collection is non-uniformly generatable but not with membership queries alone](nonuniform-generation-countable-collections.md)

## Proof depends on

- [Consistent generation with breadth requires identifiability](breadth-requires-identifiability.md)
- [Every countable collection is non-uniformly generatable but not with membership queries alone](nonuniform-generation-countable-collections.md)

## Sources

- M. Charikar, C. Pabbaraju, "Exploring Facets of Language Generation in the Limit", COLT (2025), arXiv:2411.15364.
- A. Kalavasis, A. Mehrotra, G. Velegkas, "On Characterizations for Language Generation: Interplay of Hallucinations, Breadth, and Stability", arXiv:2412.18530 (2024).
