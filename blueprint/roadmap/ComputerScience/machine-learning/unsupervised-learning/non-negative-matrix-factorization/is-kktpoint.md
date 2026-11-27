# Karush–Kuhn–Tucker point of nonnegative matrix factorization

Let $m, n, k$ be finite index sets and $X \in \mathbb{R}^{m \times n}$. A pair
$W \in \mathbb{R}^{m \times k}$, $H \in \mathbb{R}^{k \times n}$ satisfies the Karush–Kuhn–Tucker
conditions of $\min \|X - W H\|_F^2$ subject to $W, H \ge 0$ when: $W \ge 0$ and $H \ge 0$ (primal
feasibility); the [gradients](grad-w.md) $\nabla_W \ge 0$ and $\nabla_H \ge 0$ (dual
feasibility); and $W_{ia} (\nabla_W)_{ia} = 0$ and $H_{aj} (\nabla_H)_{aj} = 0$ for all entries
(complementary slackness), all inequalities entrywise.
