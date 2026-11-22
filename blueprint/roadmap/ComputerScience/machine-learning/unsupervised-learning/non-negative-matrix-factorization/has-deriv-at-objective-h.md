# Partial derivative of the NMF objective in an entry of H

Let $m, n, k$ be finite index sets, $X \in \mathbb{R}^{m \times n}$, $W \in \mathbb{R}^{m \times k}$
and $H \in \mathbb{R}^{k \times n}$. For every entry $(a, j)$, the entry $(\nabla_H)_{aj}$ of the
[gradient](grad-h.md) $2 (W^\top W H - W^\top X)$ is the derivative at $t = 0$ of
$t \mapsto \|X - W (H + t E_{aj})\|_F^2$, where $E_{aj}$ is the matrix unit.
