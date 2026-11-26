# Linear-order meeting time on the Erdős–Rényi giant component

Let $\mathcal{C}_1$ be the largest connected component of the Erdős–Rényi graph $G(n,p)$. On $\mathcal{C}_1$ run two independent continuous-time simple random walks $X, Y$ with total jump rate $1$ and stationary law $\pi$, and let $\tau_{\mathrm{meet}} = \inf\{t \ge 0 : X_t = Y_t\}$ and $t_{\mathrm{meet}}(\mathcal{C}_1) = \max_{x,y} \mathbb{E}_{x,y}[\tau_{\mathrm{meet}}]$, expectations being quenched given the graph. There are absolute constants $0 < c < C < \infty$ such that:

1. **Slightly supercritical.** If $p = (1+\varepsilon)/n$ with $\varepsilon = \varepsilon(n) \to 0$ and $\varepsilon^3 n \to \infty$, then with high probability
$$c\,n \le \mathbb{E}_{\pi\otimes\pi}[\tau_{\mathrm{meet}}] \le t_{\mathrm{meet}}(\mathcal{C}_1) \le C\,n .$$
2. **Strictly supercritical.** If $p = \lambda/n$ with $\lambda > 1$ fixed, the same bounds hold with high probability, with constants not depending on $\lambda$.
3. **Critical window.** If $|n^{1/3}(np_n - 1)| \le A_0$, then for every $\eta > 0$ there are constants $0 < c_{A_0,\eta} < C_{A_0,\eta} < \infty$ such that for all large $n$
$$\mathbb{P}\bigl(c_{A_0,\eta}\, n \le \mathbb{E}_{\pi\otimes\pi}[\tau_{\mathrm{meet}}] \le t_{\mathrm{meet}}(\mathcal{C}_1) \le C_{A_0,\eta}\, n\bigr) \ge 1 - \eta .$$

Here $n$ is the number of vertices of the whole graph, not of the component, so the meeting time is of order $n$ even though $|\mathcal{C}_1|$ is $o(n)$ in regimes 1 and 3.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

The lower bound comes from the stationary meeting rate $\sum_x \pi(x)^2$ and the degree profile of the giant. The upper bound uses the kernel–core decomposition of the giant: walks spend most time on long subdivided paths and attached trees, and resistance and commute-time estimates on the kernel show that two walks meet within order $n$ time from any pair of starting points. In population-genetic terms, $\tau_{\mathrm{meet}}$ is the pairwise coalescence time of two lineages in the voter (Moran-type) model on the giant component.

## Sources

- V. Koval, Y. Peres and P. Trapman, *Meeting and coalescence times for random walks in the largest component of the Erdős–Rényi random graph*, arXiv:2607.13183 (2026), Theorem 1 and Corollary 2. <https://doi.org/10.48550/arXiv.2607.13183>
