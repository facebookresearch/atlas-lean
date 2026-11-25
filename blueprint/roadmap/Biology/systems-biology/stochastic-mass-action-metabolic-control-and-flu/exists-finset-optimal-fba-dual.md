# Finitely many dual solutions suffice

Let $S \in \mathbb{R}^{m \times n}$ be a stoichiometric matrix, $l, u, c \in \mathbb{R}^n$ flux bounds and objective. There is a finite set $T \subseteq \mathbb{R}^m \times \mathbb{R}$ such that every
$(y, \kappa) \in T$ has $\kappa = u \cdot \alpha - l \cdot \beta$ for some $\alpha, \beta$ with
$(y, \alpha, \beta)$ [dual feasible](fba-dual-feasible.md), and for every $b \in \mathbb{R}^m$ with nonempty
[feasible set](fba-feasible.md) some $(y, \kappa) \in T$ satisfies $y \cdot b + \kappa = V(b)$, the
[optimal value](fba-value.md).
