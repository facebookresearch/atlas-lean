# Multiscale entropy regularizer

For a fractional $k$-server state on an HST, the *multiscale entropy* is a regularizer of the form $\Phi(z) = \sum_{u} \frac{w_u}{\eta_u}\, (\bar{z}_u + \delta_u) \log (\bar{z}_u + \delta_u)$, where the sum runs over the non-root nodes, $\bar{z}_u = |L_u| - z_u$ is the anti-server mass in the subtree of $u$, $\delta_u > 0$ are shift parameters and $\eta_u > 0$ are scale parameters, chosen as functions of $k$ and of the number of leaves below $u$ so that each node's term behaves like a relative entropy of the conditional anti-server distribution among the children of its parent.

## Depends on

- [Fractional k-server on a tree](fractional-k-server-polytope.md)
- [Bregman divergence (prox-function) of a distance-generating function](../../../Analysis/convex-analysis-and-variations/mirror-descent/bregman.md)

## Sources

- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085.
