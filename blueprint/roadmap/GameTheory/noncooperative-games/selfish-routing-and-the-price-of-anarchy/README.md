# Selfish routing and the price of anarchy

Nonatomic routing games: infinitely many users each control a negligible amount of traffic and choose a minimum-latency path. Equilibria are Wardrop flows; they exist when latencies are continuous, they all have the same cost when latencies are nondecreasing, they cost at most $4/3$ times the optimum when latencies are affine (Pigou's network shows this is tight), and never more than an optimal routing of twice the traffic. Braess's paradox shows that adding a link can make every user worse off.

- [Nonatomic routing instance](routing-instance.md)
- [Feasible flow for a demand vector](is-feasible.md)
- [Edge flow](edge-flow.md)
- [Edge flows of a nonnegative flow are nonnegative](edge-flow-nonneg.md)
- [Path latency](path-latency.md)
- [Cost of a flow](cost.md)
- [Weighted path latencies as a sum over edges](sum-path-latency-mul.md)
- [Cost as a sum over paths](cost-eq-sum-path-latency-mul.md)
- [Wardrop equilibrium](is-wardrop.md)
- [Existence of Wardrop equilibria](exists-is-wardrop.md)
- [Wardrop flows against a scaled demand](smul-sum-path-latency-mul-le.md)
- [Variational inequality for Wardrop equilibria](cost-le-sum-latency-mul-edge-flow.md)
- [Wardrop equilibria have unique edge latencies](latency-edge-flow-eq.md)
- [All Wardrop equilibria have the same cost](cost-eq.md)
- [Price of anarchy 4/3 for affine latencies](cost-le-of-affine.md)
- [Bicriteria bound for selfish routing](mul-cost-le-of-feasible-one-add.md)
- [Selfish routing costs at most an optimal routing of twice the traffic](cost-le-of-feasible-two.md)
- [Pigou's network](pigou.md)
- [Equilibrium flow of Pigou's network](pigou-wardrop.md)
- [Optimal flow of Pigou's network](pigou-optimal.md)
- [Edge flows in Pigou's network](pigou-edge-flow.md)
- [The equilibrium flow of Pigou's network routes one unit](pigou-is-feasible-wardrop.md)
- [The optimal flow of Pigou's network routes one unit](pigou-is-feasible-optimal.md)
- [Pigou's equilibrium flow is a Wardrop equilibrium](pigou-is-wardrop.md)
- [Cost of Pigou's equilibrium flow](pigou-cost-wardrop.md)
- [Cost of Pigou's optimal flow](pigou-cost-optimal.md)
- [Pigou's network attains the bound 4/3](pigou-cost-wardrop-eq.md)
- [Latencies of Braess's network](braess-latency.md)
- [Braess's latencies are nondecreasing](braess-latency-monotone.md)
- [Braess's network without the shortcut](braess-before.md)
- [Braess's network with the shortcut](braess-after.md)
- [Edge flows without the shortcut](braess-before-edge-flow.md)
- [Edge flows with the shortcut](braess-after-edge-flow.md)
- [Equilibrium of Braess's network without the shortcut](braess-before-is-wardrop.md)
- [Equilibrium of Braess's network with the shortcut](braess-after-is-wardrop.md)
- [Braess's paradox](braess-paradox.md)

## Related topics

- [Max-flow min-cut theorem](../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/README.md): network flows, of which routing flows are the congestion-dependent version; a feasible path flow decomposes an $s$–$t$ flow into paths.
- [Potential games](../potential-games/README.md): the atomic counterpart, where Rosenthal's potential plays the role of Beckmann's.
- [Atomic congestion games with affine delays](../atomic-congestion-games-with-affine-delays/README.md): with atomic players the affine bound becomes $5/2$.
- [No-regret dynamics](../no-regret-dynamics/README.md): price-of-anarchy bounds proved by smoothness extend to learning outcomes.
- [Mean field games](../mean-field-games/README.md): nonatomic games with a continuum of players in general; Wardrop flows are mean field equilibria, and the uniqueness of latencies is the Lasry–Lions monotonicity argument.
- [Selfish load balancing](../selfish-load-balancing/README.md): the load balancing model in which Koutsoupias and Papadimitriou introduced the price of anarchy (their coordination ratio), with makespan as social cost.
