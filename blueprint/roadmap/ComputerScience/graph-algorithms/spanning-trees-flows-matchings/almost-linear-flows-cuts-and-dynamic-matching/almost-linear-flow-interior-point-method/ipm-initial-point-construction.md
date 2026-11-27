# An initial IPM point with polynomially bounded potential

There is an $O(m)$-time algorithm that, given an integral minimum-cost flow instance $\mathcal{I}$ on $G$ with $\mathbf{u}^- < \mathbf{u}^+$ coordinatewise, demands in $\{-U, \ldots, U\}^V$ and costs and capacities in $\{-U, \ldots, U\}^E$, constructs an instance $\widetilde{\mathcal{I}}$ on a graph $\widetilde{G} \supseteq G$ with $O(m)$ edges, demands in $\{-2mU, \ldots, 2mU\}$, costs and capacities in $\{-4mU^2, \ldots, 4mU^2\}$, together with a feasible flow $\mathbf{f}^{(\mathrm{init})}$ for $\widetilde{\mathcal{I}}$ satisfying

$$
\Phi(\mathbf{f}^{(\mathrm{init})}) \le 200 m \log(mU).
$$

Moreover, from any optimal flow for $\widetilde{\mathcal{I}}$ the algorithm computes in $O(m)$ time either an optimal flow for $\mathcal{I}$ or a certificate that $\mathcal{I}$ is infeasible.

## Proof sketch

Put every edge of $G$ at the midpoint $(\mathbf{u}^-_e + \mathbf{u}^+_e)/2$ of its capacity interval and add one new vertex $v^*$. For each vertex $v$ whose demand differs from the demand routed by this flow, add one arc between $v$ and $v^*$, oriented to absorb the difference $\delta_v$, with lower capacity $0$, upper capacity $2|\delta_v|$, flow $|\delta_v|$ and cost $4mU^2$. All flows are half-integral and strictly inside their capacity intervals, so every residual capacity is at least $1/2$, the barrier sum is at most $2(m+n)\cdot 2^{\alpha}$, and the cost gap is at most $8m^3U^3 + mU^2$; this bounds $\Phi$ by $200m\log(mU)$. One unit on an auxiliary arc costs $4mU^2$, more than the spread $2mU^2$ of costs of flows in $G$, so if $\mathcal{I}$ is feasible every optimal flow of $\widetilde{\mathcal{I}}$ puts $0$ on the auxiliary arcs and restricts to an optimal flow of $\mathcal{I}$; otherwise it certifies infeasibility.

## Depends on

- [Potential function of the l1 interior point method for minimum-cost flow](l1-ipm-potential-function.md)
- [Integral minimum-cost flow instances with polynomially bounded data](integral-min-cost-flow-instance.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
