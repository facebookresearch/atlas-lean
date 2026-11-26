# Storey's estimator of the null proportion

Let $m \in \mathbb{N}$, $p_1, \dots, p_m \in \mathbb{R}$ p-values and $t \in \mathbb{R}$ a tuning parameter (used with $t \in [0, 1)$). Storey's estimator of the proportion of true nulls is

$$\hat\pi_0(t) = \frac{\#\{i : p_i > t\}}{m(1 - t)},$$

which is $0$ when $m = 0$ or $t = 1$ (division by zero).
