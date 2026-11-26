# Gold's theorem: superfinite collections are not identifiable from text

If a collection of languages contains every finite language over $U$ and at least one infinite language $L_\infty$, then it is not identifiable in the limit from positive examples. In particular the regular languages, the context-free languages and every class of the Chomsky hierarchy containing all finite languages are not identifiable from positive data.

## Proof sketch

The infinite language $L_\infty$ has no tell-tale: every finite $T \subseteq L_\infty$ is itself a language of the collection with $T \subseteq T \subsetneq L_\infty$. By Angluin's characterization (or directly by the locking-sequence argument) the collection is not identifiable.

## Depends on

- [Identification in the limit from positive examples](identification-in-the-limit.md)

## Proof depends on

- [Angluin's tell-tale characterization of identifiability in the limit](angluin-tell-tale-characterization.md)

## Sources

- E. M. Gold, "Language Identification in the Limit", Information and Control 10 (1967).
- D. Angluin, "Inductive Inference of Formal Languages from Positive Data", Information and Control 45 (1980).
