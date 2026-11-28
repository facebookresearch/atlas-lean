# Fast turnover metabolites lie on the slow manifold

In the [scaled kinetic flux profiling model](scaled-kinetic-flux-profiling-model-and-steady-state-identifiability.md) $\dot{\bar{\mathbf X}} = \mathbf K(\mathbf B - \mathbf I)\bar{\mathbf X} + \mathbf K\boldsymbol\alpha$, $\bar{\mathbf X}(0) = \mathbf 1$, suppose one metabolite turns over much faster than all others, $k_n \gg k_i$ for all $i \neq n$. The slow manifold is obtained by setting $\dot{\bar x}_n = 0$:

$$\bar x_n = \alpha_n + \sum_{j \neq n}\beta_{nj}\bar x_j.$$

**Theorem.** If $X_n$ is not the target of any labeled input edge in $\mathcal E_{\mathcal L}$, then the initial condition $\bar{\mathbf X}(0) = \mathbf 1$ lies on the slow manifold.

Consequently the trajectory stays on the slow manifold up to $O(k_i/k_n)$ corrections, the fast turnover rate $k_n$ does not affect the labeling curves to leading order, and $k_n$ cannot be estimated from such data; only when the fast metabolite receives the labeled nutrient directly is there a fast initial transient that carries information on $k_n$.

## Depends on

- [Scaled kinetic flux profiling model and steady-state identifiability](scaled-kinetic-flux-profiling-model-and-steady-state-identifiability.md)

## Expansion

If $X_n$ has no labeled input, the fractions of its inflow coming from unlabeled sources and from other metabolites sum to one, $\alpha_n + \sum_{j}\beta_{nj} = 1$, so at $t = 0$, when every pool is fully unlabeled, the slow-manifold relation holds with all $\bar x_j = 1$. The fast variable therefore starts in quasi-equilibrium and is slaved to its upstream pools for all time, which is the standard Tikhonov reduction. Practically, metabolites with small pools or large throughput behave as instantaneous relays, so their turnover rates should be fixed or dropped before fitting.

## Sources

- B. Guppy, C. Mitchell and E. Taylor, "Parameter Estimation and Identifiability in Kinetic Flux Profiling Models of Metabolism", *Bulletin of Mathematical Biology* 87(1) (2024), 7, Section 4 and Theorem 3, <https://doi.org/10.1007/s11538-024-01386-x> (preprint arXiv:2407.08844).