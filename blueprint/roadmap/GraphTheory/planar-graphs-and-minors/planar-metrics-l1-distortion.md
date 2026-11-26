# Constant-distortion L¹ embedding of planar graph metrics

There is $C\ge1$ such that the following holds for every connected simple graph on $\{0,\ldots,n-1\}$. Assume a drawing with distinct vertex points in the plane and an injective continuous arc for each oriented adjacency, with the given endpoints. Interior points cannot hit vertices, and interior points on distinct unordered edges cannot coincide. Let $\ell(u,v)=\ell(v,u)$ on all vertex pairs, with $\ell(u,v)>0$ on edges, and let $d_\ell(u,v)$ be the infimum of sums of lengths along all walks from $u$ to $v$. There is a measure space $(\Omega,\mu)$ and a map $f:V\to L^1(\Omega,\mu;\mathbb R)$ with $d_\ell(u,v)\le\|f(u)-f(v)\|_1\le C d_\ell(u,v)$ for every pair.

## Depends on

- Topological plane drawing with only the designated contacts and the weighted graph walk metric.

## Expansion

Separate the universal finite cut-family bound for the weighted planar metric: one nonnegative finite cut family, with a universal lower comparison and a universal upper comparison to all distances of the given finite metric, independent of the length ratio. Prove the exact labelled drawing/metric interface before applying it, and turn the cut family into an L¹ embedding in the final step.

## Proof outline

Bridge the two oriented arcs per adjacency to a single unoriented edge drawing and state the weighted cut estimate independently of the edge-length ratio. Establish the L¹ realization of the resulting cut metric. Do not restrict to unit lengths or to a prescribed ambient measure space.

## Sources

- [Comparator statement: `OAI.PlanarL1.planar_graph_metrics_embed_L1`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlanarL1.lean#L46-L48)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/089.md)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/PlanarL1/Embedding.lean)
