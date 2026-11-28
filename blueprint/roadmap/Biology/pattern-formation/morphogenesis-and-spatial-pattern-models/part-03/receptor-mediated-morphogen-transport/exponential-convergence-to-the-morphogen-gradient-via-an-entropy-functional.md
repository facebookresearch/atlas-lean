# Exponential convergence of the morphogen–receptor model to its steady gradient

In the Lander–Nie–Wan model of free morphogen $l$ and bound receptors $s$ on a bounded domain $\Omega \subset \mathbb{R}^n$ (diffusion $D$, unbinding $\delta$, degradation of bound morphogen $\epsilon$, source flux $\nu \ge 0$ on $\Gamma_N$, absorbing boundary $\Gamma_D$, $p > n$, initial data $l_0, s_0 \in W^1_p$ with $l_0 \ge 0$, $0 \le s_0 < 1$ and vanishing on $\Gamma_D$), let $(l_\infty, s_\infty)$ be the unique steady state.

**Theorem.** Let $\lambda_1 > 0$ be the first eigenvalue of $-\Delta$ under the homogeneous mixed boundary conditions (Neumann on $\Gamma_N$, Dirichlet on $\Gamma_D$), and set

$$
\chi = \min\left\{ D\lambda_1,\ \frac{D\lambda_1(\delta+\epsilon)}{2(D\lambda_1 + 2)} + \frac{\epsilon}{2} \right\}.
$$

There is a constant $C$ depending on $l_0, s_0, \nu, \delta, \epsilon, D, \Omega, p$ such that for every $t > 0$

$$
\|l(t) - l_\infty\|_{W^1_p} + \|s(t) - s_\infty\|_{W^1_p} \le C e^{-\chi t/2}, \qquad \|l(t) - l_\infty\|_{W^2_p} \le C \max\{t^{-1/2}, 1\}\, e^{-\chi t/2}.
$$

By the embedding $W^2_p \times W^1_p \subset C^{1,\alpha} \times C^{0,\alpha}$ for $0 \le \alpha \le 1 - n/p$, the morphogen gradient converges exponentially fast in $C^{1,\alpha}$ and the receptor occupancy in $C^{0,\alpha}$.

## Expansion

The $L^2$ step uses the Lyapunov functional

$$
\Lambda(u,v) = \tfrac12 \|u - l_\infty\|_{L^2}^2 + \int_\Omega (1 - s_\infty)(l_\infty + \delta + 2\epsilon)\Big[\Sigma(v) - \Sigma(s_\infty) - \frac{v - s_\infty}{1 - s_\infty}\Big]dx, \qquad \Sigma(x) = -\ln(1-x),
$$

whose second term is a relative entropy for the receptor occupancy. Along solutions $\Lambda + \int_0^t \mathcal{D}_\Lambda = \Lambda(l_0,s_0)$, where the dissipation $\mathcal{D}_\Lambda$ contains $D\|\nabla(u - l_\infty)\|_2^2$ and a weighted square of the binding imbalance; a Poincaré inequality with constant $\lambda_1$ gives $\chi\Lambda \le \mathcal{D}_\Lambda$, so $\Lambda$ decays like $e^{-\chi t}$ and $\|s - s_\infty\|_2^2 \le 2\Lambda/(\delta+\epsilon)$. The smoothing estimates of the heat semigroup then bootstrap the $L^2$ decay to $L^p$, $W^1_p$ and finally $W^2_p$ (the $t^{-1/2}$ factor reflects parabolic smoothing of $W^1_p$ initial data). This extends a one-dimensional Lyapunov functional to arbitrary dimension.

## Depends on

- [Steady state and global well-posedness of the Lander–Nie–Wan morphogen–receptor model](lander-nie-wan-morphogen-receptor-model-steady-state-and-well-posedness.md)

## Sources

- M. Małogrosz, *Well-posedness and asymptotic behavior of a multidimensional model of morphogen transport*, arXiv:1112.5833 (2011), Theorem 3, Lemma 1 and Lemma 4 (Section 7). <https://doi.org/10.48550/arXiv.1112.5833>
