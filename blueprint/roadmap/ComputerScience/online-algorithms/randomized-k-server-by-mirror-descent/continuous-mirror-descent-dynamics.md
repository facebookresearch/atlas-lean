# Continuous-time mirror descent for online covering

For a convex body $K$, a strictly convex regularizer $\Phi$ and a time-varying cost vector $c(t)$, the *continuous-time mirror descent* trajectory $x(t) \in K$ solves $\nabla^2 \Phi(x(t))\, \dot{x}(t) \in -c(t) - N_K(x(t))$, where $N_K(x)$ is the normal cone of $K$ at $x$. Online algorithms for $k$-server and MTS are obtained by presenting each request as a cost $c(t)$ that pushes anti-server mass away from the requested leaf until the request is served.

## Depends on

- [One-step inequality of mirror descent](../../../Analysis/convex-analysis-and-variations/mirror-descent/bregman-prox-step-le.md)
- [Bregman divergence (prox-function) of a distance-generating function](../../../Analysis/convex-analysis-and-variations/mirror-descent/bregman.md)

## Sources

- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085.
- Sébastien Bubeck, Michael B. Cohen, James R. Lee, Yin Tat Lee, "Metrical Task Systems on Trees via Mirror Descent and Unfair Gluing", SIAM Journal on Computing 50(3) (2021); SODA (2019), arXiv:1807.04404.
