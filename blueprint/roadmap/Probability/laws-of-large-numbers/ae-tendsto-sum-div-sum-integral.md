# Strong law for nonnegative, non-identically distributed variables

On a probability space, let $Y_0, Y_1, \dots$ be pairwise independent, almost surely nonnegative, square-integrable real random variables whose means $m_i = \mathbb{E}[Y_i]$ satisfy $m_i \le B$, whose variances satisfy $\operatorname{Var}(Y_i) \le C m_i$, and whose total mean $M_n = \sum_{i<n} m_i$ tends to $\infty$. Then almost surely $\sum_{i<n} Y_i / M_n \to 1$.

For Poisson counts $Y_i \sim \operatorname{Po}(m_i)$ the variance hypothesis holds with $C = 1$. The proof is the Chebyshev–Borel–Cantelli argument along a subsequence with $M_{\sigma(k)} \approx k^2$, followed by bracketing, as in Etemadi's strong law for pairwise independent indicators.
