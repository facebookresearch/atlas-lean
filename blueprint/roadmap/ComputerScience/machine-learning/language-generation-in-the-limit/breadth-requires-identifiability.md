# Consistent generation with breadth requires identifiability

Let $\mathcal{C}$ be a countable collection of languages that is not identifiable in the limit. Then no generating algorithm whose membership oracle problem is decidable (in particular, no iterative next-token generator whose conditional probabilities are computable exactly as rational numbers) generates consistently with breadth from $\mathcal{C}$, neither in the limit under adversarial enumerations nor at any rate in the statistical setting. In contrast, for every countable collection there is such an algorithm generating consistently without breadth at an exponential universal rate, and for every collection identifiable in the limit there is one generating with breadth at an almost exponential rate. If negative examples (strings outside $K$) are also available, consistent generation with breadth is achievable for every countable collection.

## Proof sketch

A generator with breadth and a decidable membership oracle problem can be turned into an identifier: its support eventually equals $K \setminus S_t$, so by querying support membership along an enumeration of $U$ one can, in the limit, recognize which language of the collection matches the support, which yields identification and contradicts non-identifiability. The positive results combine the Kleinberg–Mullainathan generator with universal-rate amplification (majority votes over independent sample batches) and, for identifiable collections, identification followed by sampling from the identified language.

## Depends on

- [Generation with breadth and the membership oracle problem](generation-with-breadth.md)
- [Generation in the limit](generation-in-the-limit.md)
- [Identification in the limit from positive examples](identification-in-the-limit.md)
- [Realizable distributions, learning curves and universal rates](../pac-learning/replicable-private-and-universal-learning/universal-multiclass-and-partial-learning/universal-learning-curves-and-littlestone-trees/universal-rate.md)

## Proof depends on

- [Every countable collection of languages is generatable in the limit](kleinberg-mullainathan-generation-theorem.md)
- [Classes with no infinite Littlestone tree are learnable at exponential rate](../pac-learning/replicable-private-and-universal-learning/universal-multiclass-and-partial-learning/universal-learning-curves-and-littlestone-trees/exponential-rate-upper-bound.md)

## Sources

- A. Kalavasis, A. Mehrotra, G. Velegkas, "On the Limits of Language Generation: Trade-Offs Between Hallucination and Mode Collapse", STOC (2025), arXiv:2411.09642.
