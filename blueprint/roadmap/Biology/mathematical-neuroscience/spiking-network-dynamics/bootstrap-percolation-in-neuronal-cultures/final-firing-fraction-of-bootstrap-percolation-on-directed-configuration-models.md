# Final firing fraction of bootstrap percolation on directed configuration models

**Model.** Neurons are the $n$ vertices of a directed configuration model $CM(n, \mathbf d^+_n, \mathbf d^-_n)$: vertex $i$ has prescribed in-degree $d^-_{n,i}$ and out-degree $d^+_{n,i}$, and in- and out-half-edges are matched uniformly at random. The empirical joint degree law converges to the law $P(j,k)$ of a pair $(D_{\mathrm{in}}, D_{\mathrm{out}})$ with finite mean $\lambda = E[D_{\mathrm{in}}] = E[D_{\mathrm{out}}]$, and the average degrees converge to $\lambda$. An initial fraction $\alpha$ of neurons, chosen at random, is activated externally. Bootstrap percolation with threshold $\Omega$: an inactive neuron fires as soon as at least $\Omega$ of its in-neighbours have fired, and fired neurons stay fired. Let $\Phi_n(\alpha)$ be the final fraction of fired neurons.

**Theorem.** Define

$$f_\alpha(y) = \lambda y - (1-\alpha)\,E\big[D_{\mathrm{out}}\,\mathbf 1\{\mathrm{Bin}(D_{\mathrm{in}}, 1-y) < \Omega\}\big], \qquad y \in [0,1],$$

and let $y^* = \max\{y \in [0,1] : f_\alpha(y) = 0\}$ (it exists since $f_\alpha(0) \le 0 < \lambda\alpha = f_\alpha(1)$).
1. If $y^* = 0$, i.e. $f_\alpha > 0$ on $(0,1]$, then $\Phi_n(\alpha) = 1 - (1-\alpha)\,P(D_{\mathrm{in}} < \Omega) + o_p(1)$: every neuron with at least $\Omega$ in-neighbours fires, while unstimulated neurons of in-degree below $\Omega$ never do (for $\Omega = 1$ and $P(0,0) = P(2,2) = \tfrac12$, $y^* = 0$ but $\Phi_n(\alpha) \to 1 - (1-\alpha)/2$).
2. If $y^* > 0$ and $y^*$ is not a local minimum of $f_\alpha$, then with high probability

$$\Phi_n(\alpha) = 1 - (1-\alpha)\,P\big(\mathrm{Bin}(D_{\mathrm{in}}, 1 - y^*) < \Omega\big) + o_p(1).$$

When $D_{\mathrm{in}}$ and $D_{\mathrm{out}}$ are independent, $f_\alpha(y) = \lambda[y - (1-\alpha)P(\mathrm{Bin}(D_{\mathrm{in}}, 1-y) < \Omega)]$, so the limit $\Phi(\alpha)$ depends only on the in-degree distribution, as observed in experiments on cultured hippocampal networks where the final active fraction jumps discontinuously in the stimulated fraction $\alpha$.

## Proof sketch

Explore the graph by revealing out-half-edges of fired neurons one at a time and matching them uniformly. Track the numbers $N^{j,k}_i(t)$ of unfired neurons of degree type $(j,k)$ that have received $i$ fired in-edges; their expected increments are smooth functions of the rescaled counts, so Wormald's differential equation method gives $N^{j,k}_i(t)/n = n^{j,k}_i(t/n) + o(1)$ uniformly up to a stopping time. The ODE solves explicitly: with $y = 1 - \tau/\lambda$ the fraction of unrevealed in-half-edges, an unstimulated neuron of in-degree $j$ has $\mathrm{Bin}(j, 1-y)$ fired in-neighbours. The process stops when the supply of unexplored fired out-half-edges, proportional to $f_\alpha(y)$, hits zero, i.e. at $y^*$; the non-degeneracy condition (no local minimum at $y^*$) ensures that the random process actually stops near the deterministic root. Neurons with fewer than $\Omega$ fired in-neighbours at $y^*$ remain silent, giving the formula.

## Sources

- Hamed Amini, "Bootstrap Percolation in Living Neural Networks", *Journal of Statistical Physics* 141 (2010), 459–475, <https://doi.org/10.1007/s10955-010-0056-z>. Preprint version: arXiv:0910.0627 (2009), main theorem, Wormald's theorem and corollary, and the lemmas solving and justifying the differential equations, <https://doi.org/10.48550/arXiv.0910.0627>.
