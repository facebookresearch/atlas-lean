# Empirical ROC rate at or above a threshold

Let $k \in \mathbb{N}$, $z_1, \dots, z_k \in \mathbb{R}$ scores and $t \in \mathbb{R}$. The empirical rate at or above $t$ is

$$\mathrm{TPR}_z(t) = \frac{\#\{i : t \le z_i\}}{k},$$

which is $0$ when $k = 0$. It is the true-positive or false-positive rate when $z$ are the positive or negative scores.
