# Bounded-treewidth metrics in finite-dimensional ℓ₁

For every integer $k\ge2$ there is a real $C\ge1$ with the following property. Let $G$ be a nonempty finite connected simple graph with positive real edge lengths $\ell$. Suppose a finite tree carries bags $B_t$ of size at most $k$, covering the vertices and both ends of every edge in at least one bag, such that the bags containing any fixed vertex induce a connected subtree. With $d_\ell$ the infimum of the sums of $\ell$ over simple paths joining each pair (including the length-zero path), there are $m\ge0$ and $F:V(G)\to\mathbb R^m$ with $d_\ell(u,v)\le\|F(u)-F(v)\|_1\le C d_\ell(u,v)$ for all $u,v$.

## Depends on

- [Treewidth convention (compare bag size and width)](has-treewidth-at-most.md)
- Positive weighted graph path metric and finite-dimensional ℓ₁ norm.

## Expansion

Separate the co-bag embedding lemma: for a positive-length connected graph and a rooted tree decomposition with bags of size at most k, give one finite ℓ₁ map that is uniformly Lipschitz on every pair and uniformly lower-bounded on pairs in the same bag, with constants depending only on k. Then combine the co-bag map with the independent separator/gluing estimate for pairs lying in different bags.

## Proof outline

Connect the finite tree-of-bags witness to the width convention $k-1$. Check that deleting closed loops from a positive-weight walk leaves a no-longer path, including in a singleton. Break the embedding proof into its decomposition, cut-weight estimates, and realization by finite ℓ₁ coordinates.

## Sources

- [Comparator statement: `OAI.BoundedTreewidthL1.main_theorem`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BoundedTreewidthL1.lean#L43-L45)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/089.md)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/TreewidthL1/Main.lean)
