# Empirical ROC rate strictly above a threshold

Let $k \in \mathbb{N}$, $z_1, \dots, z_k \in \mathbb{R}$ and $t \in \mathbb{R}$. The empirical rate strictly above $t$ is

$$\mathrm{TPR}^{>}_z(t) = \frac{\#\{i : t < z_i\}}{k},$$

which is $0$ when $k = 0$. It is the ROC coordinate at the next larger distinct score.
