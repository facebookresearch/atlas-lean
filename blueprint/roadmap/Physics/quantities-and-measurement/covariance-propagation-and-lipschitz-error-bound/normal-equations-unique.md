# For identifiable $A$ the normal equations have at most one solution

Let $A$ be a real $m \times n$ matrix such that the calibration model $y = A\theta$ is
[identifiable](identifiable.md), and let $y \in \mathbb{R}^m$. If
$\theta_1, \theta_2 \in \mathbb{R}^n$ both solve the normal equations

$$(A^\top A)\,\theta = A^\top y,$$

then $\theta_1 = \theta_2$, because the [normal matrix is injective](identifiable-normal-injective.md).
The statement asserts uniqueness only: the existence of a solution is not part of it.
