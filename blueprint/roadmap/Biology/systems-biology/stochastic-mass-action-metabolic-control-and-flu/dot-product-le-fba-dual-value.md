# Weak duality for flux balance analysis

Let $S \in \mathbb{R}^{m \times n}$ be a stoichiometric matrix, $l, u, c \in \mathbb{R}^n$ flux bounds and objective, and $b \in \mathbb{R}^m$. If $v$ is feasible ($S v = b$, $l \le v \le u$) and
$(y, \alpha, \beta)$ is [dual feasible](fba-dual-feasible.md) ($\alpha, \beta \ge 0$, $S^\top y + \alpha - \beta = c$), then

$$c \cdot v \le b \cdot y + u \cdot \alpha - l \cdot \beta.$$
