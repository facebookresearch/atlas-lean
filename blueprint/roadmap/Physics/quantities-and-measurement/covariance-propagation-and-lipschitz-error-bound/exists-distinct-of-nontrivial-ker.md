# With a nonzero kernel vector, $A\theta$ never determines $\theta$

Let $A$ be a real $m \times n$ matrix whose kernel contains a nonzero vector: $\theta_0 \ne 0$
with $A\theta_0 = 0$. Then for every parameter $\theta \in \mathbb{R}^n$ with observation
$y = A\theta$, the vector $\theta' = \theta + \theta_0$ is distinct from $\theta$ and has the same
observation:

$$\theta' \ne \theta, \qquad A\theta' = y .$$

So the calibration model $y = A\theta$ is not [identifiable](identifiable.md), and $\theta$
cannot be recovered uniquely from $y$.
