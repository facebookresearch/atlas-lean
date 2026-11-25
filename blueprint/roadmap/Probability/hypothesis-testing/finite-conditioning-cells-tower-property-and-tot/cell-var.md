# Cell Var

Let $\alpha$ be a finite set, $p : \alpha \to \mathbb{R}$ a weight, $G : \alpha \to C$ an observation map, $Y : \alpha \to \mathbb{R}$ and $c \in C$. With the cell mass $m_p(c) = \sum_{x : G(x) = c} p(x)$ and cell mean $E[Y \mid G = c]$, the within-cell variance is

$$\mathrm{Var}(Y \mid G = c) = \frac{1}{m_p(c)} \sum_{x \in \alpha,\ G(x) = c} p(x) \big(Y(x) - E[Y \mid G = c]\big)^2,$$

with the convention $t / 0 = 0$, so it is $0$ on a cell of mass $0$.
