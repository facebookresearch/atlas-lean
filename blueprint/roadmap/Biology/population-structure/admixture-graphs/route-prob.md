# Route Prob

The **routing kernel** for several lineages at one node: `k` lineages entering `X`
(backward in time) move to parents independently, lineage `i` to `a i`, with probability
`∏ i, prop X (a i)`. At a non-root node this is a probability kernel (`sum_routeProb`);
at the root there are no parents to move to, so for `k > 0` every assignment has
probability `0` and the root row has total mass `0` (`routeProb_root`,
`sum_routeProb_root`). For `k = 0` the single empty assignment has probability `1`.
