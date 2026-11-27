# An initial IPM point with polynomially bounded potential

There is an $O(m)$-time algorithm that, given an integral minimum-cost flow instance $\mathcal{I}$ on $G$ with demands in $\{-U, \ldots, U\}^V$ and costs and capacities in $\{-U, \ldots, U\}^E$, constructs an instance $\widetilde{\mathcal{I}}$ on a graph $\widetilde{G} \supseteq G$ with $O(m)$ edges, demands in $\{-2mU, \ldots, 2mU\}$, costs and capacities in $\{-4mU^2, \ldots, 4mU^2\}$, together with a feasible flow $\mathbf{f}^{(\mathrm{init})}$ for $\widetilde{\mathcal{I}}$ satisfying

$$
\Phi(\mathbf{f}^{(\mathrm{init})}) \le 200 m \log(mU).
$$

Moreover, from any optimal flow for $\widetilde{\mathcal{I}}$ the algorithm computes in $O(m)$ time either an optimal flow for $\mathcal{I}$ or a certificate that $\mathcal{I}$ is infeasible.

## Proof sketch

Add a new vertex joined to every vertex by a pair of high-capacity, very expensive arcs, so that the flow placing every edge of $G$ at the midpoint of its capacity interval and routing the resulting excesses through the new vertex is feasible. At this point every residual capacity is at least $1/2$ in the doubled instance, so the barrier sum is $O(m)$ and the cost gap is at most $\mathrm{poly}(mU)$, which bounds $\Phi$ by $200m\log(mU)$. The cost on the auxiliary arcs exceeds the cost of any flow in $G$, so an optimal flow of $\widetilde{\mathcal{I}}$ uses them only if $\mathcal{I}$ is infeasible, in which case Hoffman's condition fails.

## Depends on

- [Potential function of the l1 interior point method for minimum-cost flow](l1-ipm-potential-function.md)
- [Integral minimum-cost flow instances with polynomially bounded data](integral-min-cost-flow-instance.md)

## Proof depends on

- [Hoffman's circulation theorem](../../hoffman-circulation-theorem.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
