# Bootstrap consistency for the multivariate mean

Let $E$ be a finite-dimensional real inner product space and $X_0, X_1, \dots$ independent, identically distributed $E$-valued random vectors on a probability space with $\mathbb E\lVert X_0\rVert^2 < \infty$. Let $Z$ be an almost-everywhere measurable random vector on a probability space such that $\langle Z, t\rangle \sim N(0, \operatorname{Var}\langle X_0, t\rangle)$ for every $t \in E$ (the covariance may be singular). Then:

- $n^{-1/2}\bigl(\sum_{k<n} X_k - n\,\mathbb E X_0\bigr)$ converges in distribution to $Z$;
- for almost every data sequence $x = (X_i(\omega))$, the bootstrap statistic $\sqrt n\,(\bar x^*_n - \bar x_n)$ converges in distribution to $Z$, where $\bar x_n$ is the sample mean of $x_0, \dots, x_{n-1}$ and $\bar x^*_n$ is the mean of $n$ independent draws from their empirical distribution.
