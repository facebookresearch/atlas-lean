# Average-case reductions from secret-leakage planted clique give tight statistical-computational gaps

Assume the $k$-partite hypergraph variant of the planted clique conjecture: detecting a clique of size $k \le n^{1/2 - \epsilon}$ planted with exactly one vertex in each of $k$ known parts of a random graph (more generally of a random hypergraph) is not possible in polynomial time. Then, via average-case reductions, polynomial-time algorithms cannot beat the conjectured computational thresholds for robust sparse mean estimation, mixtures of sparse linear regressions, robust sparse linear regression, tensor PCA, variants of dense $k$-block stochastic block models, negatively correlated sparse PCA, semirandom planted dense subgraph, detection in hidden partition models, and universality of learning sparse mixtures. These reductions give hardness evidence for all polynomial-time algorithms rather than for a restricted class such as statistical query or low-degree algorithms.

## Proof sketch

Leaked partial information about the clique (its partition structure) enables reductions that rotate and recombine the adjacency matrix: Gaussian cloning and rejection kernels transform Bernoulli entries into approximately Gaussian ones, random rotations via combinatorial designs spread the planted structure into the target signal shape, and the leaked partition guarantees that the transformed planted distribution is close in total variation to the target problem's planted distribution while the null maps close to the target null.

## Proof depends on

- [Total variation distance between finite measures](../../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- M. Brennan, G. Bresler, "Reducibility and Statistical-Computational Gaps from Secret Leakage", COLT (2020), arXiv:2005.08099.
