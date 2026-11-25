# The estimated false discovery proportion is at most $q$ at the threshold

Let $c \in \mathbb{N}$, $q \in \mathbb{R}$ and $W \in \mathbb{R}^p$. If the [knockoff threshold](knockoff-threshold.md) is a real number $T$, then

$$\frac{c + \#\{j : W_j \le -T\}}{\max(|\hat S_c|, 1)} \le q,$$

where $\hat S_c$ is the [selected set](knockoff-selection.md). This is the defining property of $T$ (Barber and Candès 2015, arXiv:1404.5609, equations (1.8)-(1.9)).
