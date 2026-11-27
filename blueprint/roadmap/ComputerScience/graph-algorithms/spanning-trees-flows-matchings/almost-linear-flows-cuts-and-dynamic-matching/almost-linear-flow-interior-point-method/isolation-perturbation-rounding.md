# Random cost perturbation makes a near-optimal flow round to an optimal integral flow

Let $\mathcal{I} = (G, \mathbf{d}, \mathbf{c})$ be a minimum-cost flow instance with $\mathbf{d} \in \{-U, \ldots, U\}^V$ and $\mathbf{c} \in \{-U, \ldots, U\}^E$ such that every optimal flow has congestion at most $U$ on every edge. Let $\widetilde{\mathcal{I}} = (G, \mathbf{d}, \widetilde{\mathbf{c}})$ with $\widetilde{\mathbf{c}}_e = \mathbf{c}_e + \mathbf{z}_e$, where the $\mathbf{z}_e$ are independent and uniform on

$$
\Bigl\{\frac{1}{4m^2U^2}, \frac{2}{4m^2U^2}, \ldots, \frac{2mU}{4m^2U^2}\Bigr\}.
$$

If $\widetilde{\mathbf{f}}$ is a feasible flow for $\widetilde{\mathcal{I}}$ whose cost is at most $1/(12m^3U^3)$ above the optimum of $\widetilde{\mathcal{I}}$, and $\mathbf{f}$ is obtained by rounding each coordinate of $\widetilde{\mathbf{f}}$ to the nearest integer, then with probability at least $1/2$ the flow $\mathbf{f}$ is an optimal flow for $\mathcal{I}$.

## Proof sketch

By the isolation lemma applied to the perturbation $\mathbf{z}$, with probability at least $1/2$ the perturbed instance has a unique optimal vertex, which is integral and optimal for $\mathcal{I}$ because the perturbation is smaller than the unit integrality gap of $\mathcal{I}$. When the optimum is unique, every other vertex is worse by at least the perturbation granularity divided by polynomial factors, so a feasible flow within $1/(12m^3U^3)$ of the optimum lies within distance less than $1/2$ of the optimal vertex in every coordinate, and rounding recovers it.

## Depends on

- [Integral minimum-cost flow instances with polynomially bounded data](integral-min-cost-flow-instance.md)

## Proof depends on

- [Integral flow theorem](../../edmonds-karp-algorithm/exists-nat-max-flow.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
