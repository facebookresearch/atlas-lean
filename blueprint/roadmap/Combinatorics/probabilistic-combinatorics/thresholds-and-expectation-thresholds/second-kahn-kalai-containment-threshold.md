# Second Kahn–Kalai bound for graph containment

Let $n\ge2$ and let $H$ be a finite simple graph with at most $n$ vertices and $m=|E(H)|\ge1$. In $G(n,p)$ retain each unordered edge independently with probability $p$. Let $p_c$ be the infimum of $p\in[0,1]$ where the probability of at least one non-induced copy of $H$ is at least $1/2$. Let $p_E$ be the infimum of $p\in[0,1]$ where **every** subgraph of $H$ has expected number of actual unlabelled non-induced copies at least $1/2$. Then

$$
p_c\le\min(1,2048\mathrm e^{50} p_E(1+\log_2 m)),\qquad p_c\le6144\mathrm e^{50}p_E\log_2 n.
$$

Probability and expectation are over the product measure on all unordered edge sets.

## Depends on

- Unlabelled non-induced graph copies, independent-edge distribution, two infima at probability or expectation cutoff one half.

## Proof outline

Reconcile copy counting and isolated vertices with the native graph API, then separate the first threshold estimate and its $n$-bound consequence. This expectation threshold does not optimize arbitrary containment covers of a monotone family.

- Containment comparison from the subgraph first-moment condition, including the edge-count factor; derivation of the order-based bound.

## Sources

- [Comparator statement: `OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SecondKahnKalai.lean#L65-L69)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/176.md)
