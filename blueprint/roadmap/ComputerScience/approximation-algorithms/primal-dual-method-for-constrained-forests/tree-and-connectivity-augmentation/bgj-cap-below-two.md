# Byrka-Grandoni-Jabal Ameli: unweighted connectivity augmentation is 1.91-approximable

For every constant $\varepsilon > 0$ there is a polynomial-time $(2\ln 4-\tfrac{967}{1120}+\varepsilon)$-approximation algorithm, a factor below $1.9092+\varepsilon$, for cactus augmentation and hence for the (unweighted) connectivity augmentation problem, for every $k \ge 1$. This is the first factor below $2$ for CAP with even $k$, where the minimum cuts form a cactus rather than a tree.

## Proof sketch

CAP reduces to cactus augmentation (CacAP). Following Basavaraju et al., a CacAP instance $(G,L)$ with $t$ vertices of degree two yields a cardinality Steiner tree instance with one terminal for each degree-two cactus vertex and one Steiner node for each link: a link is adjacent to its degree-two endpoints, and two links are adjacent when they cross. A link set $A$ is feasible exactly when the terminals and $A$ induce a connected subgraph (Lemma 1), so an optimum $\mathrm{OPT}_{\mathrm{CAP}}$ yields a Steiner tree with $|\mathrm{OPT}_{\mathrm{CAP}}|+t-1$ edges, and a Steiner tree with $s$ Steiner nodes and $s+t-1$ edges yields a CacAP solution with $s$ links (Corollary 2). Using a Steiner tree algorithm as a black box gives only $3\rho_{\mathrm{ST}}-2$; instead the iterative randomized rounding algorithm of Byrka, Grandoni, Rothvoss and Sanità is analysed directly on this instance, with a marking scheme favouring Steiner-terminal edges, which yields the stated factor.

## Depends on

- [Weighted connectivity augmentation problem (WCAP)](connectivity-augmentation.md)
- [Approximation algorithms and approximation ratios](../../approximation-algorithms-and-approximation-ratios.md)
- [Cactus representations of all minimum cuts](../../../../GraphTheory/paths-cycles-connectivity/cactus-representation-and-sparse-certificates/cactus-representation-of-minimum-cuts.md)

## Proof depends on

- [Augmenting odd edge-connectivity reduces to tree augmentation](odd-cap-reduces-to-tap.md)
- [Steiner tree instances](../../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/steiner-tree/steiner-tree-instance.md)

## Sources

- Jaroslaw Byrka, Fabrizio Grandoni, Afrouz Jabal Ameli, "Breaching the 2-Approximation Barrier for Connectivity Augmentation: A Reduction to Steiner Tree", STOC (2020), arXiv:1911.02259, Theorem 1, Corollary 1, Section 2.1 (Lemma 1, Corollary 2).
- Jaroslaw Byrka, Fabrizio Grandoni, Thomas Rothvoss, Laura Sanita, "Steiner Tree Approximation via Iterative Randomized Rounding", Journal of the ACM (2013).
