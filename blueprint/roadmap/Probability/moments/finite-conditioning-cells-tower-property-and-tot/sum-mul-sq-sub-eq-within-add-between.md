# Total-variance decomposition

Let $\alpha$ and $C$ be finite, $p \ge 0$ a weight on $\alpha$, $G : \alpha \to C$ and $Y : \alpha \to \mathbb R$. For each cell $c$ let $m_c = \sum_{G(x) = c} p(x)$, $\bar Y_c = \frac{1}{m_c}\sum_{G(x) = c} p(x) Y(x)$ and $V_c = \frac{1}{m_c}\sum_{G(x) = c} p(x)(Y(x) - \bar Y_c)^2$ (both $0$ when $m_c = 0$). Then

$$\sum_x p(x)\Big(Y(x) - \sum_y p(y) Y(y)\Big)^2 = \sum_c m_c V_c + \sum_c m_c \Big(\bar Y_c - \sum_{c'} m_{c'} \bar Y_{c'}\Big)^2,$$

The weights need not sum to $1$; the identity is between these raw weighted sums. When the weights sum to $1$ it is the law of total variance, $\operatorname{Var}(Y) = \mathbb E[\operatorname{Var}(Y \mid G)] + \operatorname{Var}(\mathbb E[Y \mid G])$.
