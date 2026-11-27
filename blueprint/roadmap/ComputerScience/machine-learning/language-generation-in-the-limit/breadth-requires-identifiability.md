# Consistent generation with breadth requires identifiability

Let $\mathcal{C}$ be a countable collection of languages that is not identifiable in the limit. Then no generating algorithm whose membership oracle problem is decidable (in particular, no token-by-token generator driven by a randomized Turing machine that halts on all inputs) generates consistently with breadth from $\mathcal{C}$, neither in the limit under adversarial enumerations nor at any rate in the statistical setting. In contrast, for every countable collection there is such an algorithm generating consistently without breadth at an exponential universal rate, and for every collection identifiable in the limit there is one generating with breadth at an almost exponential rate. If negative examples are also available and complete, consistent generation with breadth is achievable for every countable collection: the adversary gives a labelled enumeration of all of $U$, in which every string eventually appears labelled by membership in $K$, or, in the statistical setting, the examples are i.i.d. draws from a distribution on $U \times \{0, 1\}$ whose marginal has full support on $U$ and whose label is membership in $K$. Negatives that may omit the strings distinguishing $K$ from other languages need not suffice, as with no informative negatives the setting is the positive-only one above.

## Proof sketch

A generator with breadth and a decidable membership oracle problem can be turned into an identifier: at step $t$, label the first $t$ strings of $U$ by membership in the support of the current generator together with $S_t$, and feed these positive and negative labels to Gold's identifier from positive and negative data. Once the support is $K \setminus S_t$ the labels are exactly membership in $K$, so the identifier converges to $K$, contradicting non-identifiability; the statistical version turns a rate for breadth into a rate for identification, which non-identifiable collections do not admit. For the positive results, the Kleinberg–Mullainathan generator, whose membership oracle problem is decidable because it outputs a single computable string, already attains exponential universal rates without batching; for identifiable collections, an identifier is boosted to almost exponential rates by running it on batches and voting, and then the generator samples from the identified language.

## Depends on

- [Generation with breadth and the membership oracle problem](generation-with-breadth.md)
- [Generation in the limit](generation-in-the-limit.md)
- [Identification in the limit from positive examples](identification-in-the-limit.md)
- [Realizable distributions, learning curves and universal rates](../pac-learning/replicable-private-and-universal-learning/universal-multiclass-and-partial-learning/universal-learning-curves-and-littlestone-trees/universal-rate.md)

## Proof depends on

- [Every countable collection of languages is generatable in the limit](kleinberg-mullainathan-generation-theorem.md)

## Sources

- A. Kalavasis, A. Mehrotra, G. Velegkas, "On the Limits of Language Generation: Trade-Offs Between Hallucination and Mode Collapse", STOC (2025), arXiv:2411.09642, Definitions 4–6, 15 and 16, Section 3.4.4, Theorems 3.2–3.5 and 3.13.
