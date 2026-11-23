# Strong duality for flux balance analysis

Let $S \in \mathbb{R}^{m \times n}$ be a stoichiometric matrix, $l, u, c \in \mathbb{R}^n$ flux bounds and objective, and $b \in \mathbb{R}^m$, and suppose the [feasible set](fba-feasible.md) $F(b) = \{v \in \mathbb{R}^n : S v = b,\ l \le v \le u\}$ is nonempty. Then there is a
[dual feasible](fba-dual-feasible.md) point $(y, \alpha, \beta)$ whose [dual objective](fba-dual-value.md)
$b \cdot y + u \cdot \alpha - l \cdot \beta$ equals the [optimal value](fba-value.md) $V(b)$.
