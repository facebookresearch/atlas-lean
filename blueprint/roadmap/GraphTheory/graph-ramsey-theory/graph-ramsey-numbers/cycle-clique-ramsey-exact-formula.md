# Exact cycle–clique Ramsey formula outside (3,3)

Let $R(C_m,K_n)$ be the infimum of the natural numbers $N$ such that every simple graph on $N$ labelled vertices either contains a non-induced $C_m$ or has a non-induced $K_n$ in its complement. For all integers $m\ge n\ge3$ with $(m,n)\ne(3,3)$,

$$
R(C_m,K_n)=(m-1)(n-1)+1.
$$

The comparator also gives the separate classical diagonal value $R(C_3,K_3)=6$.

## Depends on

- [Two-graph Ramsey number](graph-pair-ramsey.md)
- Cycle and clique containment by injective adjacency-preserving maps.

## Proof outline

Give lower and upper estimates separately (with the source's order $m\ge n$), bridge the natural infimum to the finite Ramsey value and its integer coercion, and connect the exceptional triangle–triangle statement to the existing graph API.

- General cycle–clique upper bound and sharp lower witnesses, with the exceptional classical triangle case recorded separately.

## Sources

- [Comparator statement: `OAI.CycleClique.thm_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CycleCliqueRamsey.lean#L23-L28)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/189.md)
