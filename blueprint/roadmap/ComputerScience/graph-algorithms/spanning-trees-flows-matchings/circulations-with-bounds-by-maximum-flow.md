# Flows with bounds and supplies by maximum flow

Let $G$ be a finite directed graph with real bounds $l \le u$ on its arcs and prescribed net inflows $b_v$ with $\sum_v b_v = 0$, and let $B$ be its vertex–arc incidence matrix, the column of an arc $e$ from $t(e)$ to $h(e)$ being $\mathbf 1_{h(e)} - \mathbf 1_{t(e)}$ (zero for a loop). Put $r = b - Bl$, the net inflow still required after sending $l$. Add a source $s^*$ with an arc $s^* \to v$ of capacity $-r_v$ for each $v$ with $r_v < 0$, a sink $t^*$ with an arc $v \to t^*$ of capacity $r_v$ for each $v$ with $r_v > 0$, and give each arc $e$ of $G$ capacity $u_e - l_e$. A flow $f$ with $l \le f \le u$ and $Bf = b$ exists if and only if the maximum $s^*$–$t^*$ flow value equals $\sum_{v : r_v > 0} r_v$; then $f = l + g$ for the restriction $g$ of any maximum flow to the arcs of $G$. If moreover $l$, $u$ and $b$ are integral, an integral such $f$ exists.

Proof. $f$ is feasible exactly when $g = f - l$ satisfies $0 \le g \le u - l$ and $Bg = r$. Such a $g$ together with saturated source and sink arcs is an $s^*$–$t^*$ flow of value $\sum_{r_v > 0} r_v$, which is the capacity of the cut $\{s^*\}$; conversely a flow of that value saturates every source and sink arc, so its restriction satisfies $Bg = r$. For integrality, all capacities of the auxiliary network are then integral, and an integral maximum flow gives an integral $g$.

## Proof depends on

- [Max-flow min-cut theorem](../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md): maximum flows exist and are bounded by cut capacities.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Aggregation of parallel arcs: flows on an arc-indexed graph correspond to flows on vertex pairs with summed capacities, with disaggregation back to the arcs.
- An integral maximum flow exists for integral capacities on a finite directed graph.

## Background

- [Hoffman's circulation theorem](hoffman-circulation-theorem.md): the cut condition for the same feasibility problem.

## Sources

- J. Kleinberg and É. Tardos, *Algorithm Design*, Pearson, 2005; lecture slides by K. Wayne, §7.7 Circulation with supplies, demands, and lower bounds, <https://www.cs.princeton.edu/~wayne/kleinberg-tardos/pdf/07NetworkFlowII-2x2.pdf>
