# Feasible flux balance problem attains its optimum

Let $S \in \mathbb{R}^{m \times n}$ be a stoichiometric matrix, $l, u, c \in \mathbb{R}^n$ flux bounds and objective, and $b \in \mathbb{R}^m$, and suppose the [feasible set](fba-feasible.md) $F(b) = \{v \in \mathbb{R}^n : S v = b,\ l \le v \le u\}$ is nonempty. Then there is
$v \in F(b)$ with $c \cdot w \le c \cdot v$ for every $w \in F(b)$, and the [optimal value](fba-value.md) $V(b)$ equals
$c \cdot v$.
