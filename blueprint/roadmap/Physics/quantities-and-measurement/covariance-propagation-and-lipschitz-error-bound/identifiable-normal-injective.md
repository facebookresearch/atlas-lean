# For identifiable $A$ the normal matrix $A^\top A$ is injective

Let $A$ be a real $m \times n$ matrix such that the calibration model $y = A\theta$ is
[identifiable](identifiable.md) ($\theta \mapsto A\theta$ injective). Then the map
$\theta \mapsto (A^\top A)\,\theta$ on $\mathbb{R}^n$ is injective. Indeed, if
$(A^\top A)\,\theta = 0$, then

$$0 = \theta^\top A^\top A\, \theta = (A\theta) \cdot (A\theta) = \sum_{k=1}^{m} (A\theta)_k^2,$$

so $A\theta = 0$, and $\theta = 0$ by identifiability.
