# Continuous-time mirror descent for online covering

Let $K \subseteq \mathbb{R}^N$ be a compact convex set, let $\Phi : K \to \mathbb{R}$ be a twice differentiable, strongly convex regularizer whose inverse Hessian $\nabla^2 \Phi(x)^{-1}$ is continuous on $K$, and let $c : [0, \infty) \to \mathbb{R}^N$ be a continuous time-varying cost vector. The *continuous-time mirror descent* trajectory from $x_0 \in K$ is an absolutely continuous path $x(t) \in K$ with $x(0) = x_0$ and $\nabla^2 \Phi(x(t))\, \dot{x}(t) \in -c(t) - N_K(x(t))$ for almost every $t \ge 0$, where $N_K(x)$ is the normal cone of $K$ at $x$. Such a trajectory exists, and it is unique when moreover $\nabla^2 \Phi$ is Lipschitz and $c$ is locally Lipschitz.

For metrical task systems on a tree, $K$ is a convex body whose first coordinates range over the probability distributions on the states, $c(t)$ is the current task's service cost vector on those coordinates (and $0$ on the others), and the algorithm pays the service cost $\int \langle c(t), x(t) \rangle\, dt$ plus the movement of $x$ in a norm that equals the transportation distance between the induced distributions. The $k$-server algorithm is a separate instance: there $K$ is an assignment polytope of anti-server coordinates, a request at a leaf $\ell$ is the constant cost $c(t) = e_{\ell}$ on the anti-server coordinate of $\ell$, and the dynamics are stopped as soon as that coordinate has been driven down far enough for the request to be served.

## Depends on

- [Bregman divergence (prox-function) of a distance-generating function](../../../Analysis/convex-analysis-and-variations/mirror-descent/bregman.md)

## Sources

- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085.
- Sébastien Bubeck, Michael B. Cohen, James R. Lee, Yin Tat Lee, "Metrical Task Systems on Trees via Mirror Descent and Unfair Gluing", SIAM Journal on Computing 50(3) (2021); SODA (2019), arXiv:1807.04404.
