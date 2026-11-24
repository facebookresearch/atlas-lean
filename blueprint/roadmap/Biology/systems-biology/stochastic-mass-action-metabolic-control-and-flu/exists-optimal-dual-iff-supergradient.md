# Shadow prices

Let $S \in \mathbb{R}^{m \times n}$ be a stoichiometric matrix, $l, u, c \in \mathbb{R}^n$ flux bounds and objective, let $b \in \mathbb{R}^m$ have nonempty [feasible set](fba-feasible.md), and let
$y \in \mathbb{R}^m$. There are $\alpha, \beta$ such that $(y, \alpha, \beta)$ is [dual feasible](fba-dual-feasible.md) and
minimizes the [dual objective](fba-dual-value.md) at $b$ among all dual feasible points if and only if
$V(b') \le V(b) + y \cdot (b' - b)$ for every $b'$ with nonempty feasible set, where $V$ is the
[optimal value](fba-value.md): the metabolite prices of the optimal dual solutions are exactly the
supergradients of the optimal value. This is the shadow-price reading of the dual solution of the flux
balance linear programme (for the flux balance formulation, see Orth, Thiele & Palsson 2010).
