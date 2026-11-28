# Reconciliation graph and full subtrees

A **reconciliation graph** for a gene tree $G$ and a dated species tree $S'$ is an acyclic directed bipartite graph with *mapping nodes* $(u, x, v)$, where $u \in V(G)$, $x \in V(S')$ and $v \in \mathbb{N}^3$ is an event count vector, and *event nodes* labelled by an event type (contemporary, speciation, duplication, transfer, no-event, speciation-loss, transfer-loss), whose roots are mapping nodes on the root of $G$. A **full subtree** is a connected subtree rooted at such a root in which every mapping node keeps exactly one child, every event node keeps all its children, and every leaf is a leaf of the graph.

**Theorem.** Given the matrix of event count vectors from the Pareto dynamic program, a backtracking procedure builds, in $O(|V(S)|^3 |V(G)|^5)$ time and space, a reconciliation graph whose full subtrees are in bijection with the reconciliations whose event count vectors are retained: every full subtree depicts such a reconciliation, every such reconciliation is depicted by a full subtree, and the graph has the minimum number of vertices among graphs with this property (To et al. 2015, Lemma 2 and Theorem 2).

Consequently the **support** of an event, the fraction of reconciliations in the space that contain it, can be computed by one post-order and one pre-order traversal of the graph without enumerating the possibly exponentially many reconciliations.

## Depends on

- [Pareto-optimal versus parsimonious DTL reconciliations](pareto-optimal-versus-parsimonious-dtl-reconciliations.md)

## Expansion

Each full subtree has one root and one child per mapping node, which are exactly the defining conditions of a reconciliation tree, and reconciliation trees depict reconciliations one-to-one. In the post-order pass each node receives the number of partial full subtrees below it (products over event-node children, sums over mapping-node children); the pre-order pass propagates the number of complete reconciliations through each node, and dividing by the total gives the event support.

## Sources

- T.-H. To, E. Jacox, V. Ranwez and C. Scornavacca, *A fast method for calculating reliable event supports in tree reconciliations via Pareto optimality*, BMC Bioinformatics 16 (2015), 384, Definitions 3–5, Lemma 2 and Theorem 2. <https://doi.org/10.1186/s12859-015-0803-x> (PMCID: PMC4647304)
