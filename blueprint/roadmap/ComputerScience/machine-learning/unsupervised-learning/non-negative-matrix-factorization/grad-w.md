# Gradient of the NMF objective with respect to W

Let $n, k$ be finite index sets, $X \in \mathbb{R}^{m \times n}$, $W \in \mathbb{R}^{m \times k}$
and $H \in \mathbb{R}^{k \times n}$. The gradient of the [objective](objective.md)
$\|X - W H\|_F^2$ with respect to $W$ is the $m \times k$ matrix
$\nabla_W = 2 (W H H^\top - X H^\top)$.
