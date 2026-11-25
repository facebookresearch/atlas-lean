# Weighted probability of an event

Let $E$ be a finite set and $\varphi : E \times \{0,1\} \to \mathbb{R}$. The weighted probability of an event $S \subseteq \{0,1\}^E$ is the total [product weight](pweight.md) of its configurations,

$$P_\varphi(S) = \sum_{\omega \in S} \prod_{x \in E} \varphi_x(\omega(x)).$$

When $\varphi \ge 0$ and $\varphi_x(0) + \varphi_x(1) = 1$ for every $x$, this is the probability of $S$ under the product measure whose coordinate $x$ has law $\varphi_x$.
