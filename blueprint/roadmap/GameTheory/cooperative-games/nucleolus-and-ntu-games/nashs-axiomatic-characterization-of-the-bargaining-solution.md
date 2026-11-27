# Nash's axiomatic characterization of the bargaining solution

Let $X \subseteq \mathbb{R}^2$ be compact and convex, $d \in X$, and suppose some $x \in X$ has $x > d$. The maximizer of the Nash product $(x_1 - d_1)(x_2 - d_2)$ over $\{x \in X : x \ge d\}$ is unique and is strongly Pareto optimal, symmetric, invariant under positive affine rescaling of each player's utility, and independent of irrelevant alternatives. Conversely it is the unique bargaining solution satisfying weak (or strong) Pareto optimality, symmetry, invariance under positive affine rescaling of each player's utility (applied to both $X$ and $d$) and independence of irrelevant alternatives.

## Proof sketch

Rescale so that $d = 0$ and the Nash solution is $(1, 1)$; the supporting line $x_1 + x_2 = 2$ is tangent there. In the symmetric triangle bounded by this line, symmetry and Pareto optimality force $(1,1)$, and independence of irrelevant alternatives transfers this to $X$.

## Depends on

- [Existence and uniqueness of the Nash bargaining solution](../nash-bargaining-solution/existence-of-a-nash-product-maximizer.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
