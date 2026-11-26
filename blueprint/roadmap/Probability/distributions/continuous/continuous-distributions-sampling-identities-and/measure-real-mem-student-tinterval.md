# Exact nominal coverage `1 - α`

Let $X_0, \dots, X_{n-1}$ be real random variables on $(\Omega, P)$ with $n \ge 2$, and let $\mu \in \mathbb{R}$ and $\sigma > 0$. Assume $X_0, \dots, X_{n-1}$ are mutually independent and each has law $N(\mu, \sigma^2)$ under $P$. Write $\bar{X}_n(\omega) = \frac{1}{n} \sum_{i=0}^{n-1} X_i(\omega)$ and $s_n(\omega) = \sqrt{\frac{1}{n-1} \sum_{i=0}^{n-1} \bigl(X_i(\omega) - \bar{X}_n(\omega)\bigr)^2}$, with $x / 0 = 0$, and let $t_{n-1}$ be the Student-t distribution with $n - 1$ degrees of freedom, with density $\frac{\Gamma(n/2)}{\sqrt{(n-1)\pi}\, \Gamma((n-1)/2)} \bigl(1 + \frac{t^2}{n-1}\bigr)^{-n/2}$. Let $q \ge 0$ and $\alpha \in \mathbb{R}$ with

$$t_{n-1}\bigl( (-\infty, -q) \bigr) = \frac{\alpha}{2}, \qquad t_{n-1}\bigl( (q, \infty) \bigr) = \frac{\alpha}{2}.$$

Then

$$P\Bigl( \mu \in \Bigl[ \bar{X}_n - \frac{q\, s_n}{\sqrt{n}},\ \bar{X}_n + \frac{q\, s_n}{\sqrt{n}} \Bigr] \Bigr) = 1 - \alpha.$$

The tail conditions say that $q = t_{n-1, 1-\alpha/2}$ is the upper $\alpha/2$ quantile of $t_{n-1}$.
