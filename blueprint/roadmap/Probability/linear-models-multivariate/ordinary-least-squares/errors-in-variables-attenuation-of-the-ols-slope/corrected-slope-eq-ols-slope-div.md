# Corrected slope as the naive slope over the estimated reliability ratio

Let $x, y \in \mathbb{R}^n$ be indexed by a finite set of size $n$ with $S_{xx} = \sum_i (x_i - \bar x)^2 \neq 0$, and let $\sigma_u^2 \in \mathbb{R}$. Then the corrected slope equals the naive least-squares slope divided by the estimated reliability ratio:

$$\frac{S_{xy}}{S_{xx} - n\,\sigma_u^2} = \frac{S_{xy}/S_{xx}}{(s_x^2 - \sigma_u^2)/s_x^2}, \qquad s_x^2 = S_{xx}/n,$$

with the convention that a quotient by $0$ is $0$.
