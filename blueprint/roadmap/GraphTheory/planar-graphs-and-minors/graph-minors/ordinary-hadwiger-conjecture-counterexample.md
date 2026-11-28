# Counterexample to the ordinary chromatic Hadwiger inequality

It is not true that for every finite simple graph $G$ on $\{0,\ldots,m-1\}$ the chromatic number satisfies $\chi(G)\le h(G)$. Here $h(G)$ is the maximum order of a clique realized by disjoint connected branch sets with an inter-set edge between each pair, and it is embedded in the extended natural numbers when compared with $\chi(G)$. This concerns ordinary colouring, not fractional or list colouring.

## Depends on

- Ordinary extended chromatic number and the connected branch-set definition of clique-minor order.

## Proof depends on

- [A finite quantitative witness](quantitative-hadwiger-counterexamples.md)

## Proof outline

Take one quantified witness and convert its strict natural inequality to the negation of the extended order inequality, carrying the explicit no-infinity clause. Do not change a separately stated conjecture's polarity.

## Sources

- [Comparator statement: `OAI.HadwigerCounterexample.not_hadwiger_conjecture`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HadwigerCounterexample.lean#L49-L53)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/157.md)
