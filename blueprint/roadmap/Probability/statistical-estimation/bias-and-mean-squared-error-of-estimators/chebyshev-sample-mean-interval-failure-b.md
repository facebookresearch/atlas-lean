# Chebyshev confidence interval for the sample mean

Let $(\Omega, \mu)$ be a probability space, $n \ge 1$, and let $X_1, \dots, X_n : \Omega \to \mathbb{R}$ be mutually independent and square integrable, with common mean $\mathbb{E}[X_i] = m$ and common variance $\operatorname{Var}(X_i) = \sigma^2$, where $\sigma > 0$. Let $\bar{X} = \frac{1}{n} \sum_{i=1}^n X_i$ and $k > 0$. Then the interval $\bar{X} \pm k \sigma / \sqrt{n}$ fails to cover $m$ with probability at most $1/k^2$:

$$\mu\Bigl( m \notin \Bigl[ \bar{X} - \frac{k \sigma}{\sqrt{n}},\ \bar{X} + \frac{k \sigma}{\sqrt{n}} \Bigr] \Bigr) \le \frac{1}{k^2}.$$
