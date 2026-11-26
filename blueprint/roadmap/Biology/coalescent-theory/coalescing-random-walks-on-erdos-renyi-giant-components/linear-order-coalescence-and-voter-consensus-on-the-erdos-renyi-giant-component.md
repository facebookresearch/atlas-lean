# Linear-order coalescence and voter consensus on the Erdős–Rényi giant component

Consider the continuous-time voter model on the largest component $\mathcal{C}_1$ of $G(n,p)$, each vertex updating at rate $1$ by copying a uniformly chosen neighbour, started from all-distinct opinions, and let $\tau_{\mathrm{cons}}$ be the consensus time. Expectations are quenched given the graph. There are absolute constants $0 < c < C < \infty$ such that:

1. if $p = \lambda/n$ with $\lambda > 1$ fixed, then with high probability $c\,n \le \mathbb{E}[\tau_{\mathrm{cons}}] \le C\,n$;
2. if $p = (1+\varepsilon)/n$ with $\varepsilon \to 0$ and $\varepsilon^3 n \to \infty$, then with high probability $c\,n \le \mathbb{E}[\tau_{\mathrm{cons}}] \le C\,n$;
3. if $|n^{1/3}(np_n - 1)| \le A_0$, then for every $\eta > 0$ there are $0 < c_{A_0,\eta} < C_{A_0,\eta}$ with $\mathbb{P}\bigl(c_{A_0,\eta}\,n \le \mathbb{E}[\tau_{\mathrm{cons}}] \le C_{A_0,\eta}\,n\bigr) \ge 1-\eta$ for all large $n$.

In all three regimes the same bounds hold for the full coalescence time of coalescing random walks started with one particle at every vertex, i.e. for the time to the most recent common ancestor of the whole population in the dual genealogy.

## Depends on

- [Linear-order meeting time on the Erdős–Rényi giant component](linear-order-meeting-time-on-the-erdos-renyi-giant-component.md)
- [Coalescing random walks dual to the voter model on a finite graph](../structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

By voter–coalescing-walk duality, consensus time and full coalescence time have the same law. The full coalescence time is at least a pairwise meeting time and is compared to meeting and hitting times by Oliveira's inequalities and the Kanade–Mallmann-Trenn–Sauerwald comparison. In the slightly supercritical regime a direct comparison loses a logarithm; this is avoided by first reducing to a bounded number of clusters with Oliveira's bound, using the diameter of the giant, and only then applying a small-particle comparison.

## Sources

- V. Koval, Y. Peres and P. Trapman, *Meeting and coalescence times for random walks in the largest component of the Erdős–Rényi random graph*, arXiv:2607.13183 (2026), Theorem 1 and Corollary 2. <https://doi.org/10.48550/arXiv.2607.13183>
