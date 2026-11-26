# Separate counterexamples to infinite matroid covering and packing criteria

On subsets of $E=\mathbb Z\times\coprod_{m\ge0}\{f:\{0,1\}^m\to\{0,1\}\}$, for two matroids on common ground set $F$, let covering mean their independent sets can be chosen to cover $F$ and packing mean they have disjoint spanning sets. There exist $F$ and such a pair invalidating the equivalence between covering and the assertion that for every $Y\subseteq F$, packing in the two restrictions to $Y$ implies covering $Y$ there. Separately, there exist $F'$ and a pair on it invalidating the equivalence between packing and the assertion that every $Y\subseteq F'$ admitting a covering in the two contractions onto $Y$ admits a packing there. Contraction onto $Y$ means dual, restrict to $Y$, then dual. The two witnesses need not coincide.

## Depends on

- Infinite matroid restriction, contraction onto a retained subset, covering and packing conditions and the two proposed biconditionals.

## Proof outline

Factor each failed biconditional into the direction disproved and a concrete witness. Keep the local intermediate matroids as restrictions in one clause and contractions in the other.

- Separate finite-index-family obstruction for covering and for packing, with their local criteria; duality transfer if used by the construction.

## Sources

- [Comparator statement: `OAI.InfiniteMatroidCounterexample.separate_covering_packing_counterexamples`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InfiniteMatroidCorollaries.lean#L119-L125)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/185.md)
