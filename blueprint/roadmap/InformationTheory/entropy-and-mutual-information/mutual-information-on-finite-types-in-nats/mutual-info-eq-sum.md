# Mutual Info eq sum

Let $\alpha$ and $\beta$ be finite types and let $p$ be a probability mass function on $\alpha \times \beta$, with marginals $p_X(x) = \sum_{y} p(x, y)$ and $p_Y(y) = \sum_{x} p(x, y)$. Then the mutual information of $p$ in nats is the finite sum

$$I_{\mathrm{nats}}(p) = \sum_{x \in \alpha} \sum_{y \in \beta} p(x, y) \ln \frac{p(x, y)}{p_X(x) \, p_Y(y)},$$

with the conventions $\ln 0 = 0$ and $t / 0 = 0$, so terms with $p(x, y) = 0$ contribute $0$.
