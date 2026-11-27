# Variance of a compound sum

Let $N$ be a random variable with values in $\{0, 1, 2, \dots\}$ and $E[N^2] < \infty$, and let $X_1, X_2, \dots$ be i.i.d. real random variables with $E[X_1^2] < \infty$, independent of $N$. Then the compound sum $S = \sum_{i=1}^{N} X_i$ (with $S = 0$ when $N = 0$) is square integrable, with

$$E[S] = E[N]\,E[X_1], \qquad \operatorname{Var}(S) = E[N] \operatorname{Var}(X_1) + \operatorname{Var}(N)\, E[X_1]^2.$$

No bound on $N$ and no moment generating function is needed. Proof. By independence, $E[S^2 \mathbf 1_{\{N = n\}}] = P(N = n)\, E[(X_1 + \dots + X_n)^2] = P(N = n)\,(n \operatorname{Var}(X_1) + n^2 E[X_1]^2)$ for each $n$, and summing these nonnegative terms over $n$ gives $E[S^2] = E[N]\operatorname{Var}(X_1) + E[N^2] E[X_1]^2 < \infty$. The same decomposition, dominated by $\sum_{i \le N} |X_i|$ whose mean is $E[N]\,E|X_1|$, gives $E[S]$, and subtracting $E[S]^2$ gives the variance. The second term vanishes when $E[X_1] = 0$, and the formula then reduces to $E[N]\operatorname{Var}(X_1)$; with a nonzero mean the count's own variability enters.

## Background

- [Wald's second equation](../../Probability/martingales/wald-s-equations/wald-s-second-equation/wald-second-equation.md): the zero-mean case for a stopping time, where $N$ need not be independent of the claims.

## Sources

- R. Kaas, M. Goovaerts, J. Dhaene and M. Denuit, *Modern Actuarial Risk Theory*, Springer; author recap sheet of chapters 1–6, compound distributions, <https://www1feb-uva.nl/ke/act/people/kaas/Recap123456.pdf>
