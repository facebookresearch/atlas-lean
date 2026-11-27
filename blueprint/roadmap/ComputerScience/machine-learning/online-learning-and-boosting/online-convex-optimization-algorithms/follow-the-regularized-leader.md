# Follow the regularized leader

Let $K$ be a subset of a real normed space, $\psi : K \to \mathbb{R}$ a regularizer and $\ell_0, \ell_1, \ldots : K \to \mathbb{R}$ losses. A sequence $x_0, x_1, \ldots$ is a run of follow the regularized leader (FTRL) if for every $t$, $x_t \in K$ minimizes $\psi(y) + \sum_{s<t}\ell_s(y)$ over $y \in K$. So $x_t$ depends only on $\ell_0, \ldots, \ell_{t-1}$, and bounds for FTRL hold against adaptive adversaries. Runs exist when $K$ is compact and nonempty and $\psi$ and the losses are continuous, and the run is unique when $K$ is convex, $\psi$ is $\mu$-strongly convex with $\mu > 0$ and the losses are convex. With $\psi = 0$ and finitely many points this is follow the leader.

## Depends on

- [Regularized Follow-the-Leader / Online Mirror Descent regret](../regularized-follow-the-leader-online-mirror-descent-regret.md)

## Sources

- Francesco Orabona, "A Modern Introduction to Online Learning", lecture notes, 2019.
- Elad Hazan, "Introduction to Online Convex Optimization", MIT Press, 2022.
