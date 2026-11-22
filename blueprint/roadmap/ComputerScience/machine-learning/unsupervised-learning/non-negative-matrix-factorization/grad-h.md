# Gradient of the NMF objective with respect to H

Let $m, k$ be finite index sets, $X \in \mathbb{R}^{m \times n}$, $W \in \mathbb{R}^{m \times k}$
and $H \in \mathbb{R}^{k \times n}$. The gradient of the [objective](objective.md)
$\|X - W H\|_F^2$ with respect to $H$ is the $k \times n$ matrix
$\nabla_H = 2 (W^\top W H - W^\top X)$.
