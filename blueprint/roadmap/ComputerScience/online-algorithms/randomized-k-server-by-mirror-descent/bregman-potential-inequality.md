# Bregman-divergence potential for mirror descent

Along a continuous-time mirror descent trajectory $x(t)$ in $K$ with regularizer $\Phi$ and costs $c(t)$, for every fixed comparator $y \in K$, $\frac{d}{dt} D_\Phi(y \,\|\, x(t)) \le \langle c(t), y - x(t) \rangle$, where $D_\Phi$ is the Bregman divergence. Hence the online service cost $\int \langle c(t), x(t) \rangle\,dt$ exceeds the comparator's service cost $\int \langle c(t), y\rangle\,dt$ by at most $D_\Phi(y \,\|\, x(0))$, and a moving comparator $y(t)$ adds at most $\sup_{x, x' \in K}\|\nabla\Phi(x) - \nabla\Phi(x')\|_*$ times its total movement $\int \|\dot y\|\,dt$, where $\|\cdot\|_*$ is the norm dual to the movement norm $\|\cdot\|$ (Bubeck, Cohen, Lee, Lee and Mądry use the modified divergence $\hat D_\Phi(y \,\|\, x) = D_\Phi(y \,\|\, x) - \Phi(y)$, which changes at rate $-\langle \nabla\Phi(x), \dot y\rangle$, and bound $\sup_x \|\nabla\Phi(x)\|_*$).

## Proof sketch

Differentiate $D_\Phi(y\|x) = \Phi(y) - \Phi(x) - \langle \nabla\Phi(x), y - x\rangle$ in $t$: the derivative is $-\langle \nabla^2\Phi(x)\dot{x}, y - x\rangle$. Substituting the dynamics, the cost term gives $\langle c, y - x\rangle$ and the normal-cone term is nonpositive because $y - x$ points into $K$. Integrating gives the static bound, and moving $y$ changes $D_\Phi(y\|x)$ at rate $\langle \nabla \Phi(y) - \nabla\Phi(x), \dot{y}\rangle$, which Hölder's inequality bounds by the dual norm of $\nabla \Phi(y) - \nabla\Phi(x)$ times the speed of $y$.

## Depends on

- [Continuous-time mirror descent for online covering](continuous-mirror-descent-dynamics.md)
- [Bregman divergence (prox-function) of a distance-generating function](../../../Analysis/convex-analysis-and-variations/mirror-descent/bregman.md)

## Sources

- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085, Section 2.1 and equation (2.9).
- Sébastien Bubeck, Michael B. Cohen, James R. Lee, Yin Tat Lee, "Metrical Task Systems on Trees via Mirror Descent and Unfair Gluing", SIAM Journal on Computing 50(3) (2021); SODA (2019), arXiv:1807.04404.
