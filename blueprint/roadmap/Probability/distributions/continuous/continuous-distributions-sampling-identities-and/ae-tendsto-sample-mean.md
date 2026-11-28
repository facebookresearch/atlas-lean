# Strong law of large numbers

Let $(X_i)_{i \in \mathbb{N}}$ be real random variables on a measurable space $\Omega$ with a measure $P$, and let $\bar{X}_n(\omega) = \frac{1}{n} \sum_{i=0}^{n-1} X_i(\omega)$ (which is $0$ for $n = 0$) be the sample mean of the first $n$ observations. Suppose $X_0$ is integrable, the $X_i$ are pairwise independent, and every $X_i$ has the same distribution as $X_0$ under $P$. Then for $P$-almost every $\omega$,

$$\bar{X}_n(\omega) \to \int X_0 \, dP \quad (n \to \infty).$$

Pairwise independence suffices, and $P$ need not be normalized.
