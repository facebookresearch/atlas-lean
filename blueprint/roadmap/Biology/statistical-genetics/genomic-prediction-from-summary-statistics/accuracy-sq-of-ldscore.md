# Polygenic-score accuracy in the LD-score model

Let $(h^2, \beta, \varepsilon)$ be an [LD-score model](../ld-score-regression/model.md) with $N \ne 0$ individuals and $M \ne 0$ markers, and let $X$ be a real $N \times M$ matrix with [orthogonal standardized columns](has-orthogonal-columns.md). Then the [squared accuracy](accuracy-sq.md) of the [derived effect-estimate model](of-ldscore.md) is

$$r_g^2 = \frac{N h^2}{N h^2 + M (1 - h^2)},$$

with the convention $x/0 = 0$. The Daetwyler–Dudbridge formula $N h^2 / (N h^2 + M)$ takes the residual variance to be $1$ instead of $1 - h^2$.
