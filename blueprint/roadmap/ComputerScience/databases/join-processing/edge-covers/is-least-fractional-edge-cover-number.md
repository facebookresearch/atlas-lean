# Attainment of the fractional edge cover number

For a finite named join hypergraph, there is a [fractional edge cover](is-fractional-edge-cover.md) of total weight $\rho^*$, and every fractional edge cover has total weight at least $\rho^*$. This includes empty headings and the empty family of relations.

To see why the minimum exists, take weight one on each relation. Every vertex belongs to some heading, so this is feasible. Now clip any feasible weight vector at one coordinatewise: if a vertex meets a weight at least one, that relation alone still covers it; otherwise all its incident weights are unchanged. Clipping never increases cost. Thus it suffices to minimise on the feasible part of the unit cube. This set is nonempty and closed in a compact cube, and the sum of the weights is continuous.
