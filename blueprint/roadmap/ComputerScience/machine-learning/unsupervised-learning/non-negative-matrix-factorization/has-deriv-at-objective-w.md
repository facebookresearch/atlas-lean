# Partial derivative of the NMF objective in an entry of W

Let $m, n, k$ be finite index sets, $X \in \mathbb{R}^{m \times n}$, $W \in \mathbb{R}^{m \times k}$
and $H \in \mathbb{R}^{k \times n}$. For every entry $(i, a)$, the entry $(\nabla_W)_{ia}$ of the
[gradient](grad-w.md) $2 (W H H^\top - X H^\top)$ is the derivative at $t = 0$ of
$t \mapsto \|X - (W + t E_{ia}) H\|_F^2$, where $E_{ia}$ is the matrix unit.
