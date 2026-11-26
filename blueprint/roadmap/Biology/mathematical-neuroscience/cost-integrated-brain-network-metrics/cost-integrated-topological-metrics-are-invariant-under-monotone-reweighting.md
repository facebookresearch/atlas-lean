# Cost-integrated network metrics are invariant under monotone reweighting

Let $G$ be a fully weighted undirected network on $N_V \ge 2$ nodes (for example a functional brain network), with association matrix $W = (w_{ij})$, $w_{ij} = w_{ji}$, $w_{ii} = 0$, and let $N_I = N_V(N_V - 1)/2$ be the number of node pairs. For a cost level $k$ in the discrete cost domain

$$\Omega_K = \left\{ \tfrac{1}{N_I}, \tfrac{2}{N_I}, \dots, 1 \right\},$$

let the thresholding map $\gamma(W, k)$ return the unweighted graph whose edges are the $k N_I$ node pairs of largest weight, ties being broken by a fixed ordering of the pair indices (equivalently, the pairs whose percentile rank among the weights is at most $k$). For any topological metric $T$ defined on unweighted graphs (global or local efficiency, clustering, path length, ...) and any probability mass function $p$ on $\Omega_K$, the **cost-integrated metric** is

$$T_p(W) = \sum_{k \in \Omega_K} T\big(\gamma(W, k)\big)\, p(k).$$

**Invariance (Proposition 1 of the source).** If $h : \mathbb{R} \to \mathbb{R}$ is strictly increasing and is applied elementwise to the off-diagonal weights, then

$$T_p\big(h(W)\big) = T_p(W).$$

In particular two networks with proportional weights, $W' = c W$ with $c > 0$, or related by any rescaling or shift used to standardize association weights into the unit interval, have identical cost-integrated metrics, whatever their weighted costs (mean weights).

## Expansion

The graph $\gamma(W, k)$ depends on $W$ only through the ranks of the off-diagonal weights (with the index tie-break), and a strictly increasing map preserves these ranks, so $\gamma(h(W), k) = \gamma(W, k)$ for every $k \in \Omega_K$; summing against $p$ gives the claim. The proof does not use the form of $T$ or of $p$, which in the source is either uniform on $\Omega_K$ or a beta-binomial law on the number of edges. The null cost is excluded from $\Omega_K$ because every edge-based metric vanishes there. The invariance is also the limitation of the method: cost-integration separates topology from connectivity strength completely, so differences in mean connectivity must be reported separately (as the weighted cost), and cost-specific topological differences can be averaged out. Networks being compared must have the same number of positive weights, or the integration domain must be restricted to the common range of costs.

## Sources

- C. E. Ginestet, T. E. Nichols, E. T. Bullmore and A. Simmons, *Brain network analysis: separating cost from topology using cost-integration*, PLoS ONE 6(7) (2011), e21570. DOI: <https://doi.org/10.1371/journal.pone.0021570>. PMCID: PMC3145634.
