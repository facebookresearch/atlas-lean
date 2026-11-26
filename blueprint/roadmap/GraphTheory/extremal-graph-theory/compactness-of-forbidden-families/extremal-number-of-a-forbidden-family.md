# Extremal number and compactness of a forbidden family

A family $\mathcal F$ here is a finite set of finite simple graphs, each on its own finite vertex set. A simple graph is $\mathcal F$-free if no member embeds as a subgraph, not necessarily as an induced subgraph. Write $\operatorname{ex}(n,\mathcal F)$ for the supremum in $\mathbb N$ of the number of edges over $\mathcal F$-free hosts on $n$ vertices, with value $0$ for an empty set of hosts.

The family is compact when some $F\in\mathcal F$ and real $A>0$ satisfy $\operatorname{ex}(n,F)\le A\operatorname{ex}(n,\mathcal F)$ for all sufficiently large $n$. The reverse inequality follows from $\mathcal F$-freeness. A cyclic family is one in which every member contains a cycle.

## Depends on

- [Extremal number for one forbidden graph](../extremal-number-for-one-forbidden-graph.md)

## Expansion

Extend the single-graph extremal number to a family of possibly different orders, characterize maxima over labelled hosts, and prove the relation with relabeling and singleton families. The maximum is over subgraph exclusion, not induced exclusion.

## Sources

- [Pinned forbidden-family model](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/J_CompactnessConjecture.lean#L10-L44)
