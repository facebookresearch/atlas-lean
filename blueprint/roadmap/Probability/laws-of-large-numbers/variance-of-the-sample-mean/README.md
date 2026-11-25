# Variance of the sample mean

Let $X_0, X_1, X_2, \dots$ be mutually independent real random variables on a measure space $(\Omega, \mu)$, typically a probability space, each with the same distribution as $X_0$, and suppose $X_0$ is square-integrable. Then for every integer $n \ge 1$, the sample mean $\frac{1}{n} \sum_{i=0}^{n-1} X_i$ has variance $\operatorname{Var}(X_0)/n$, variances being taken with respect to $\mu$. Square-integrability is needed only for $X_0$, since identical distribution transfers it to every sample.

## Idea

Averaging reduces noise. Variances of independent variables add, so the sum of $n$ samples has variance $n \operatorname{Var}(X_0)$, and dividing by $n$ divides the variance by $n^2$. The standard deviation of the sample mean is therefore $\sigma / \sqrt{n}$, where $\sigma^2 = \operatorname{Var}(X_0)$. With Chebyshev's inequality this proves the weak law of large numbers,

$$P\Big(\Big|\frac{1}{n} \sum_{i<n} X_i - \mathbb{E}[X_0]\Big| \ge \varepsilon\Big) \le \frac{\sigma^2}{n \varepsilon^2},$$

and it is the $1/\sqrt{n}$ error rate of Monte Carlo estimation: halving the error takes four times as many samples.

## Statements

- [Variance of the sample mean of i.i.d. samples](variance-sample-mean-of-iid.md)
