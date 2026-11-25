# Dual feasibility for flux balance analysis

Let $S \in \mathbb{R}^{m \times n}$ and $c \in \mathbb{R}^n$. A triple $(y, \alpha, \beta)$ with
$y \in \mathbb{R}^m$ (metabolite prices) and $\alpha, \beta \in \mathbb{R}^n$ (prices of the upper and
lower flux bounds) is dual feasible for flux balance analysis when $\alpha \ge 0$, $\beta \ge 0$ and
$S^\top y + \alpha - \beta = c$.
