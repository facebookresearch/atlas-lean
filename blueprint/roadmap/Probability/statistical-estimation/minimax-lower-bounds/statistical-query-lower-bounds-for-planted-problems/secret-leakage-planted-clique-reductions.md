# Average-case reductions from secret-leakage planted clique give tight statistical-computational gaps

Assume Brennan and Bresler's Conjecture 2.3(4), the $k$-partite hypergraph variant of the planted clique conjecture: for $s \ge 3$ and $k = o(\sqrt{n})$, no $\mathrm{poly}(n)$-time algorithm solves $k\text{-HPC}^s(n, k, 1/2)$, the problem of testing between an $s$-uniform Erdős–Rényi hypergraph on $n$ vertices with hyperedge probability $1/2$ and the same hypergraph with a $k$-clique planted with one uniformly random vertex in each of the $k$ known parts of size $n/k$ of a fixed partition. Part (4) is the strongest assumption of their Conjecture 2.3: it implies parts (1)–(3), including the graph case (Section 12.1). Then, via average-case reductions, polynomial-time algorithms cannot beat the conjectured computational thresholds for robust sparse mean estimation, mixtures of sparse linear regressions, robust sparse linear regression, tensor PCA, variants of dense $k$-block stochastic block models, negatively correlated sparse PCA, semirandom planted dense subgraph, detection in hidden partition models, and universality of learning sparse mixtures. These reductions give hardness evidence for all polynomial-time algorithms rather than for a restricted class such as statistical query or low-degree algorithms.

## Proof sketch

Leaked partial information about the clique (its partition structure) enables reductions that rotate and recombine the adjacency matrix: Gaussian cloning and rejection kernels transform Bernoulli entries into approximately Gaussian ones, random rotations via combinatorial designs spread the planted structure into the target signal shape, and the leaked partition guarantees that the transformed planted distribution is close in total variation to the target problem's planted distribution while the null maps close to the target null.

## Proof depends on

- [Total variation distance between finite measures](../../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- M. Brennan, G. Bresler, "Reducibility and Statistical-Computational Gaps from Secret Leakage", COLT (2020), arXiv:2005.08099, Conjecture 2.3 and Section 12.1.
