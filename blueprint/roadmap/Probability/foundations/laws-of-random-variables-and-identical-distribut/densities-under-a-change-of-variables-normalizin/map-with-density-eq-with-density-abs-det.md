# Change of variables for densities

Let $E$ be a finite-dimensional real normed space with its Borel σ-algebra and $\mu$ an additive Haar measure on $E$. Let $T : E \to E$ be a measurable bijection with measurable inverse such that $T^{-1}$ has Fréchet derivative $S'(x)$ at every $x \in E$. For every function $p : E \to [0, \infty]$, the pushforward under $T$ of the measure with density $p$ with respect to $\mu$ has density $x \mapsto p(T^{-1}(x))\, \lvert \det S'(x) \rvert$:

$$T_{\#}(p \cdot \mu) = \bigl(x \mapsto p(T^{-1}(x))\, \lvert \det S'(x) \rvert\bigr) \cdot \mu.$$

Neither measurability of $p$ nor invertibility of $S'(x)$ is required.
