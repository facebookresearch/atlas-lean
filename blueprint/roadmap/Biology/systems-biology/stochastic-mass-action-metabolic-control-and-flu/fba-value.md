# Optimal value of flux balance analysis

Let $S \in \mathbb{R}^{m \times n}$ be a stoichiometric matrix, $l, u, c \in \mathbb{R}^n$ flux bounds and objective, and $b \in \mathbb{R}^m$. The optimal value of flux balance analysis is

$$V(b) = \sup \{c \cdot v : S v = b,\ l \le v \le u\},$$

taken to be $0$ when the problem is infeasible (the set is empty).
