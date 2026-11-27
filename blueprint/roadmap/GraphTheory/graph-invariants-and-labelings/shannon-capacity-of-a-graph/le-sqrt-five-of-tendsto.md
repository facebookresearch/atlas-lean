# The Shannon capacity of the pentagon is at most $\sqrt 5$

If graphs $H_k$ on words of length $k + 1$ over the pentagon, such as the [strong powers](strong-power.md) $C_5^{\boxtimes(k+1)}$, satisfy the hypothesis of [Feasible values multiply along strong powers](pow-mem-theta-feasible.md), and $\alpha(H_k)^{1/(k+1)} \to \theta$, then $\theta \le \sqrt 5$. For the strong powers, $\theta$ is the [Shannon capacity](has-shannon-capacity.md) $\Theta(C_5)$: this is the upper half of [Lovász's theorem](shannon-capacity-pentagon.md) $\Theta(C_5) = \sqrt 5$. It follows from [Lovász's bound](le-lovasz-theta-of-tendsto.md) $\Theta(G) \le \vartheta(G)$ and [$\vartheta(C_5) \le \sqrt 5$](lovasz-theta-cycle-graph-five-le.md). The lower half comes from the five-element independent set $\{(i, 2i)\}$ of $C_5 \boxtimes C_5$ (Shannon) together with the existence of the limit.

## Sources

- L. Lovász, *On the Shannon capacity of a graph*, IEEE Trans. Inform. Theory 25 (1979), 1–7.
