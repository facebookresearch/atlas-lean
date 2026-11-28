# Variance of the inner product on a convex body and its polar

For $n \in \mathbb{N}$ and a set $K \subseteq \mathbb{R}^n$ (with the Euclidean inner product), let

$$K^\circ = \{y \in \mathbb{R}^n : \langle x, y\rangle \le 1 \text{ for all } x \in K\}$$

be the polar of $K$, and let $m = |K|\,|K^\circ|$ be the product of their Lebesgue measures, each taken as a real number (an infinite measure counts as $0$). The inner product variance of $K$ is

$$\operatorname{Var}(K) = \frac{1}{m}\int_K \int_{K^\circ} \langle x, y\rangle^2 \, dy\, dx - \left(\frac{1}{m}\int_K \int_{K^\circ} \langle x, y\rangle \, dy\, dx\right)^2.$$

When $K$ and $K^\circ$ are measurable with positive finite measure and $\langle x, y\rangle^2$ is integrable on $K \times K^\circ$, for instance when $K$ is a convex body with the origin in its interior, so that $K^\circ$ is one too, this is $\mathbb{E}\langle X, Y\rangle^2 - (\mathbb{E}\langle X, Y\rangle)^2$ for independent $X$ uniform on $K$ and $Y$ uniform on $K^\circ$. Otherwise it is only the formula above: division by $m = 0$ gives $0$, and an integral of a non-integrable function is $0$.
