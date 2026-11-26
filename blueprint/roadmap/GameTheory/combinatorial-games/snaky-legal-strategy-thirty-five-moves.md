# Legal Snaky strategy by the thirty-fifth Maker move

Maker and Breaker start from empty finite sets of cells of $\mathbb Z^2$. A policy $\sigma(r,M,B)$ supplies a new cell outside both sets for **every** remaining-move count $r$ and finite sets $M,B$. In round $k$ (starting from zero), propose $\sigma(35-k,M_k,B_k)$ and add it to $M_k$; then add the proposed reply $\beta_k$ to $B_k$. For any infinite reply list with the first 34 replies unclaimed after their respective Maker moves, Maker's set after the 35th Maker move has cardinality 35, contains an image of $\{(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)\}$ under a square symmetry and translation, and is disjoint from Breaker's set after 34 replies. At each complete round count $k<35$ the two sets are disjoint and Breaker's set has cardinality $k$. No legality is required of the reply after the last Maker move.

## Depends on

- Infinite lattice placement of the six cells, remaining-move policy and state recursion, and legal reply prefixes.

## Proof depends on

- [Recursive 35-move certificate data](snaky-thirty-five-move-certificate.md)
- A 35-move empty-board construction (opening plus certified subgames) and extraction of a total fresh-cell policy with disjointness/cardinality invariants.

## Expansion

Compare the opening and conditional templates to the 35-round game state. Keep the original source `OriginalResult` theorem distinct from the four standalone conditional templates in its `Main` module. Expose the generic game induction and terminal Maker-before-Breaker state separately.

## Sources

- [Comparator statement: `OAI.SnakyConditional.snaky_winning_strategy_with_legal_states`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SnakyConditional.lean#L44-L55)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/187.md)
- [Actual pinned solution of the 35-move legal-state target](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/GameTheory/SnakyConditional/OriginalResult.lean)
