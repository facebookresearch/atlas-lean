# Chain rule, second-coordinate orientation

Let $\alpha$ and $\beta$ be finite sets and let $p$ be a probability mass function on $\alpha \times \beta$, the joint law of $(X, Y)$, with second marginal $p_Y(b) = \sum_{a} p(a, b)$. Then, in bits,

$$H(X, Y) = H(Y) + H(X \mid Y),$$

where $H(X, Y) = -\sum_{a, b} p(a, b) \log_2 p(a, b)$, $H(Y) = -\sum_{b} p_Y(b) \log_2 p_Y(b)$, and

$$H(X \mid Y) = -\sum_{b \in \beta} \sum_{a \in \alpha} p(a, b) \log_2 \frac{p(a, b)}{p_Y(b)},$$

every term with zero probability contributing $0$.
