# Within-cell weighted variance expression

Let $\alpha$ be a finite set, $p : \alpha \to \mathbb{R}$ a signed weight, $G : \alpha \to C$ an observation map, $Y : \alpha \to \mathbb{R}$ and $c \in C$. With the cell mass $m_p(c) = \sum_{x : G(x) = c} p(x)$ and the weighted cell average $\bar Y_c = \frac{1}{m_p(c)} \sum_{x : G(x) = c} p(x) Y(x)$, the within-cell expression is

$$V_p(c) = \frac{1}{m_p(c)} \sum_{x \in \alpha,\ G(x) = c} p(x) \big(Y(x) - \bar Y_c\big)^2,$$

with the convention $t / 0 = 0$, so it is $0$ on a cell of mass $0$.

For nonnegative weights and a cell of positive mass, $V_p(c)$ is the conditional variance of $Y$ given $G = c$ under the normalized weights. With signed weights it is only an expression and can be negative: in one cell with weights $(2, -1)$ and observations $(0, 1)$ it equals $-2$.
