# Power Constraint

Let $(\Omega, \mu)$ be a measure space, $E$ a normed abelian group, $X : \Omega \to E$ and $P \in \mathbb{R}$. The input $X$ satisfies the power constraint with budget $P$ under $\mu$ if

$$P \ge 0 \quad\text{and}\quad \int^{-} \lVert X(\omega) \rVert^2 \, d\mu(\omega) \le P,$$

where the integral is the lower Lebesgue integral in $[0, \infty]$. No measurability or integrability of $X$ is assumed.

For $E = \mathbb{R}$, $\lVert x \rVert^2 = x^2$, so the condition is the scalar power bound $P \ge 0$ and $\int^{-} X^2 \, d\mu \le P$. The condition $P \ge 0$ is needed because in $[0, \infty]$ a negative budget would be read as $0$.
