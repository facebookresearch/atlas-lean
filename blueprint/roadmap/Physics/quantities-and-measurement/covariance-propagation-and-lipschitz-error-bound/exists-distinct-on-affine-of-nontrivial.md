# A nonzero kernel vector in $V$ defeats uniqueness on $\theta_0 + V$

Let $A$ be a real $m \times n$ matrix, $\theta_0 \in \mathbb{R}^n$ and $V$ a linear subspace of
$\mathbb{R}^n$, and suppose that some $v_0 \in V$ with $v_0 \ne 0$ satisfies $Av_0 = 0$. Then for
every parameter $\theta$ of the affine subspace
$\theta_0 + V = \{\theta : \theta - \theta_0 \in V\}$ with observation $y = A\theta$, the vector
$\theta' = \theta + v_0$ satisfies

$$\theta' \ne \theta, \qquad \theta' \in \theta_0 + V, \qquad A\theta' = y .$$

So $A$ is not [identifiable on](identifiable-on-affine.md) $\theta_0 + V$, and a unique estimate
of the parameter within $\theta_0 + V$ requires identifiability on that space.
