# Escape along a strip under power-law competition

**Setting.** In the [two interacting birth–death processes](recurrence-and-transience-of-two-interacting-birth-death-processes.md) model, the chain $\xi = (\xi_1,\xi_2)$ on $\mathbb{Z}_+^2$ jumps from $(x,y)$ to $(x+1,y)$ at rate $F(x)G(y)$, to $(x,y+1)$ at rate $F(y)G(x)$, and down in each coordinate at rate $1$. Take power-law self-growth and competition,

$$F(x) = (x+1)^{\lambda_1}, \qquad G(x) = (x+1)^{-\lambda_2}, \qquad 0 < \lambda_1 < \lambda_2.$$

**Theorem.**

1. If $0 < \lambda_1 \le 1$, the chain is transient and non-explosive. Let $k \in \mathbb{Z}_+$ satisfy $\lambda_1 + k\lambda_2 \le 1 < \lambda_1 + (k+1)\lambda_2$. With a probability $\tilde p \in (0,1)$ depending on the initial state, $\xi$ is eventually absorbed in the horizontal strip $\{y \le k\}$ and visits each line $\{y = j\}$, $j \le k$, at unboundedly large times; with probability $1 - \tilde p$ the same holds for the vertical strip $\{x \le k\}$.
2. If $\lambda_1 > 1$, the chain is transient and explodes almost surely. There is a random integer $m$ and a random time $\tau$ before the explosion time such that $\min(\xi_1(t),\xi_2(t)) = m$ for all $t \ge \tau$: the chain explodes along a single horizontal or vertical ray.

In both regimes one population wins and goes to infinity while the competitor is held at a bounded level, the strip width $k$ being set by how strongly the winner suppresses the loser's birth rate ($k$ increases as $\lambda_2$ decreases).

**Auxiliary facts.** For $0 < \lambda_1 \le 1$ and $\lambda_1 < \lambda_2$ the time to reach the boundary satisfies $\mathbb{E}(\tau_0 \mid \xi(0) = (x,y)) \le \min(x,y)/\varepsilon$ for some $\varepsilon > 0$, where $\tau_0 = \inf\{t : \min(\xi_1,\xi_2) = 0\}$, so the minimum hits $0$ at unboundedly large times almost surely. If $\lambda_1 + k\lambda_2 \le 1$, a coordinate started at $0$ reaches level $k$ almost surely.

## Depends on

- [Recurrence and transience of two interacting birth–death processes](recurrence-and-transience-of-two-interacting-birth-death-processes.md)

## Expansion

When $\xi_1 = x$ is large and $\xi_2 = j$ is small, the loser's birth rate is $(j+1)^{\lambda_1}(x+1)^{-\lambda_2} \to 0$ while the winner's is $(x+1)^{\lambda_1}(j+1)^{-\lambda_2}$. Along the strip $\{y = j\}$ the winner behaves like a one-dimensional birth–death process with birth rate of order $x^{\lambda_1}$, transient for $\lambda_1 > 0$ and explosive iff $\sum x^{-\lambda_1} < \infty$, i.e. $\lambda_1 > 1$. Since the loser falls back at rate $1$ and climbs at rate of order $x^{-\lambda_2}$, while the winner is near $x$ it sits at level $j$ with probability of order $x^{-j\lambda_2}$; the winner spends time of order $x^{-\lambda_1}$ near each $x$, so the expected total time at level $j$ is of order $\sum_x x^{-\lambda_1 - j\lambda_2}$, which diverges exactly when $\lambda_1 + j\lambda_2 \le 1$; this produces the threshold $k$. Lyapunov-function estimates make these heuristics rigorous.

## Sources

- Mikhail Menshikov and Vadim Shcherbakov, "Long term behaviour of two interacting birth-and-death processes", arXiv:1605.09607 (2016), Theorem 3 (Section 2), Propositions 2–5, Corollary 1 and Lemmas 1–2 (Section 3), <https://doi.org/10.48550/arXiv.1605.09607>.
