# Quantitative clique-minor and chromatic separation

For every $M\in\mathbb N$ there is $m\ge\max(M,5)$ and a simple graph on $m$ vertices with independence number at most two and touching-matching number less than $m/100$. A touching matching consists of disjoint two-vertex edges with an edge of the graph between every distinct pair of chosen edges. Let $h(G)$ be the largest number of disjoint connected branch sets with an edge between each pair, and let $\chi(G)$ be the chromatic number. The witness satisfies $h(G)<26m/75+2/3<m/2\le\chi(G)$ and $h(G)<\chi(G)$, with finite $\chi(G)$ equal to the image of its natural value; the fractional bounds are rational comparisons.

## Depends on

- Connected branch-set clique minors, touching matchings, independence number and the finite value of the extended chromatic number.

## Expansion

Separate the matching–minor bound: for every finite nonempty simple graph $G$, with $m=|V(G)|$ and touching-matching number $c$, prove $h(G)\le(m+4c+2)/3$ in the rationals, with no independence-number restriction. For the separate chromatic consequence assume $\alpha(G)\le2$, $c<m/100$, and $m\ge5$. These give $h(G)<26m/75+2/3<m/2\le\chi(G)$: the independence bound is used for $m/2\le\chi(G)$, not for the matching–minor inequality. Apply these estimates to the constructed family only after checking all three additional hypotheses.

## Proof outline

State the construction's independence and touching-matching inequalities separately, connect the branch-set formulation to the graph-minor API, and recover the chromatic lower bound from independent color classes. Preserve the fixed rational offsets.

## Sources

- [Comparator statement: `OAI.HadwigerCounterexample.exists_counterexamples`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HadwigerCounterexample.lean#L38-L48)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/157.md)
- [Matching–minor proposition and its conditional chromatic consequence](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/HadwigerMatching/Main.lean#L9-L20), and [application to the constructed graphs](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/HadwigerCounterexample/Main.lean#L101-L119).
