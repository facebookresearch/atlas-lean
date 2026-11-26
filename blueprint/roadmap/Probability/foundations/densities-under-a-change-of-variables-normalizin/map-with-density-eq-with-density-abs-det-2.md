# Map with Density eq with Density abs det jacobian Matrix symm

Let $d \in \mathbb{N}$ and let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a measurable bijection with measurable inverse such that $T^{-1}$ is differentiable everywhere. For every $p : \mathbb{R}^d \to [0, \infty]$, the pushforward under $T$ of the measure with density $p$ with respect to Lebesgue measure $\lambda$ is

$$T_{\#}(p \cdot \lambda) = \bigl(x \mapsto p(T^{-1}(x))\, \lvert \det J_{T^{-1}}(x) \rvert\bigr) \cdot \lambda,$$

where $J_{T^{-1}}(x)$ is the Jacobian matrix of $T^{-1}$ at $x$.
