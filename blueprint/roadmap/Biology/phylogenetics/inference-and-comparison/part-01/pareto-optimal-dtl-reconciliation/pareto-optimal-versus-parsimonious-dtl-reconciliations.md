# Pareto-optimal versus parsimonious DTL reconciliations

Let $G$ be a gene tree and $S'$ a subdivided dated species tree. A reconciliation $\alpha$ of $G$ with $S'$ (built from speciation, duplication, transfer, speciation-loss, transfer-loss and no-event steps) has an **event count vector** $v(\alpha) = (d, t, l) \in \mathbb{N}^3$ counting its duplications, transfers and losses. Order vectors componentwise, with $v < v'$ meaning $v \le v'$ and $v \ne v'$.

- $\alpha$ is **Pareto-optimal** if no reconciliation $\alpha'$ has $v(\alpha') < v(\alpha)$.
- For a cost vector $c = (\delta, \tau, \lambda)$ of strictly positive reals, $\operatorname{cost}(\alpha, c) = v(\alpha) \cdot c$, and $\alpha$ is **parsimonious** for $c$ if no reconciliation has strictly smaller cost.

**Fact.** Every reconciliation parsimonious for some positive cost vector is Pareto-optimal, but the converse fails: there are gene and species trees with a Pareto-optimal reconciliation of event count vector $(1, 2, 4)$ that is parsimonious for no strictly positive cost vector (To et al. 2015, Remark 2 and Fig. 3).

The event count vectors of all reconciliations parsimonious for some cost vector $c$ whose ratio vector $r(c) = (\lambda/\tau, \delta/\tau, \lambda/\delta)$ lies in a given box $[r_m, r_M]$ (componentwise $r_m \le r(c) \le r_M$) can be computed by dynamic programming over pairs (gene node, species node) in $O(|V(S)|^2 |V(G)|^5)$ time and $O(|V(S)|^2 |V(G)|^3)$ space (Theorem 1).

## Expansion

If $v(\alpha') < v(\alpha)$ then $v(\alpha') \cdot c < v(\alpha) \cdot c$ for any strictly positive $c$, so a dominated reconciliation is never parsimonious. Conversely, parsimonious reconciliations for positive costs are exactly the Pareto points on the lower convex hull of the attainable event count vectors; a Pareto point strictly inside the hull is optimal for no linear cost. The dynamic program carries, for every mapping $(u,x)$, the list of non-dominated vectors, combining children's lists with vector addition.

## Sources

- T.-H. To, E. Jacox, V. Ranwez and C. Scornavacca, *A fast method for calculating reliable event supports in tree reconciliations via Pareto optimality*, BMC Bioinformatics 16 (2015), 384, Remark 2, Fig. 3 and Theorem 1. <https://doi.org/10.1186/s12859-015-0803-x> (PMCID: PMC4647304)
