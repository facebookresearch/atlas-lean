# The $O(1/N)$ rate of mirror-prox with the step $\alpha / (\sqrt{2} L)$

In the setting of the [ergodic rate](mirror-prox-average-le.md) with $L > 0$ and the step $\gamma = \alpha/(\sqrt{2}L)$, if $V_{z_0}(u) \le \Theta$ for all $u \in Z$ (for instance $\Theta = \max_Z \omega - \min_Z \omega$ when $z_0$ minimizes $\omega$ on $Z$), then for $N \ge 1$

$$
\max_{u \in Z} F(u)(\bar w_N - u) \le \frac{\sqrt{2}\,\Theta L}{\alpha N} .
$$

Each step costs two evaluations of $F$ and two prox steps. The $O(1/N)$ rate beats the $O(1/\sqrt{N})$ black-box lower bound for nonsmooth problems because the structure is used: a convex function given as $\max_y \phi(x, y)$ with smooth convex-concave $\phi$ is minimized through the monotone operator $(\partial_x \phi, -\partial_y \phi)$ of the saddle-point problem. In the Euclidean setup the method is Korpelevich's extragradient method.

## Background

- [Constant-step rate of mirror descent](../mirror-descent/mirror-descent-exists-le-sqrt.md): the $O(1/\sqrt{N})$ rate for nonsmooth problems that this rate improves on under Lipschitz continuity of the operator.

## Sources

- A. Nemirovski, *Prox-method with rate of convergence O(1/t) for variational inequalities with Lipschitz continuous monotone operators and smooth convex-concave saddle point problems*, SIAM J. Optim. 15(1) (2004), 229–251; author PDF at <https://www2.isye.gatech.edu/~nemirovs/SIOPT_042562-1.pdf>, Section 3, Theorem 3.2, efficiency estimate (3.9), with the step (3.2) and $\Theta = \Theta(z_0)$ of (2.13); the saddle-point form (3.10) is [the saddle-point accuracy of mirror-prox](mirror-prox-saddle-le-sqrt-two.md).
