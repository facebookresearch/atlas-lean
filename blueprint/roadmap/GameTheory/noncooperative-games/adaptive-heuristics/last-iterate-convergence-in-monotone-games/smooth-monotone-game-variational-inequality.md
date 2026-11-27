# Smooth monotone game and monotone variational inequality

A continuous game has players $i = 1, \dots, m$ with nonempty compact convex action sets $\mathcal{X}_i \subseteq \mathbb{R}^{d_i}$ and continuously differentiable convex-in-own-action costs $f_i(x_i, x_{-i})$. Its gradient operator is $F(x) = \bigl(\nabla_{x_1} f_1(x), \dots, \nabla_{x_m} f_m(x)\bigr)$ on $\mathcal{Z} = \prod_i \mathcal{X}_i$. The game is monotone if $\langle F(x) - F(y), x - y \rangle \ge 0$ for all $x, y \in \mathcal{Z}$, and $L$-smooth if $\lVert F(x) - F(y) \rVert \le L \lVert x - y\rVert$. A point $x^\star$ is a Nash equilibrium iff it solves the variational inequality $\langle F(x^\star), x - x^\star\rangle \ge 0$ for all $x \in \mathcal{Z}$. Two-player zero-sum games with convex-concave payoffs are monotone.

## Depends on

- [Mixed Nash equilibrium](../../nash-s-theorem/is-mixed-nash.md)

## Sources

- Y. Cai, A. Oikonomou, W. Zheng, "Finite-Time Last-Iterate Convergence for Learning in Multi-Player Games", NeurIPS 2022; full version "Tight Last-Iterate Convergence of the Extragradient and the Optimistic Gradient Descent-Ascent Algorithm for Constrained Monotone Variational Inequalities", arXiv:2204.09228.
- A. Nemirovski, "Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems", SIAM Journal on Optimization 15(1) (2004).
