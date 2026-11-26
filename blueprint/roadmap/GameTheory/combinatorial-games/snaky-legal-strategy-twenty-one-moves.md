# Legal Snaky strategy by the twenty-first Maker move

Maker and Breaker start from empty finite sets of cells of $\mathbb Z^2$. There exists a policy $\sigma(r,M,B)$ choosing a cell outside $M\cup B$ for every count $r$ and finite sets $M,B$. In zero-indexed round $k$ add $\sigma(21-k,M_k,B_k)$ to Maker's set, then add reply $\beta_k$ to Breaker's. For every reply sequence whose first 20 replies are unclaimed after their respective Maker moves, the 21st Maker move brings Maker's count to 21, produces a translated image by one of the eight square symmetries of $\{(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)\}$ within Maker's set, and leaves it disjoint from Breaker's 20-reply set. For each complete round count $k<21$ both sets are disjoint and Breaker's count is exactly $k$. Board and quantifiers are infinite; there is no requirement on the reply after the final Maker move.

## Depends on

- Six-cell placements, infinite-board fresh move and alternating round semantics with only the first 20 replies tested.

## Proof depends on

- Height-21 certificate and correctness of its transition semantics, with all-legal-play preservation of disjointness and counts.

## Expansion

Separate the finite strategic certificate and its verification from lifting to a policy on all finite positions (including off-certificate states), then identify the terminal Maker and previous Breaker states. Do not impose a finite board or infer a matching lower bound.

## Sources

- [Comparator statement: `OAI.SnakyPrototype.snaky_winning_strategy_21_with_legal_states`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SnakyTwentyOne.lean#L45-L56)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/187.md)
- [Source certificate-to-policy assembly](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/GameTheory/SnakyTwentyOne/Main.lean)
