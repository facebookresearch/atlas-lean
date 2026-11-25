# Central limit theorem for multinomial proportions

Let $p = (p_1, \dots, p_K)$ be a probability vector (zero entries allowed) and let $X_1, X_2, \dots$ be i.i.d. random vectors in $\mathbb{R}^K$ with $P(X_1 = e_k) = p_k$, where $e_k$ is the $k$-th standard basis vector. Then $E[X_1] = p$ and $\operatorname{Cov}(X_1) = \operatorname{diag}(p) - pp^{\mathsf T}$, and $\sqrt n(\hat p_n - p) \to N(0, \operatorname{diag}(p) - pp^{\mathsf T})$ in distribution, where $\hat p_n = n^{-1}\sum_{i \le n} X_i$ is the vector of multinomial proportions. The limit covariance is singular, since $\mathbf 1^{\mathsf T}(\hat p_n - p) = 0$; coordinates with $p_k = 0$ converge to the point mass at $0$.

## Proof depends on

- [Multivariate central limit theorem](tendsto-in-distribution-inv-sqrt-smul-su.md): applied to the one-hot vectors, whose covariance may be singular.

## Sources

- J. Brunner, *Random Vectors Part Two* (lecture slides, STA 442/2101), University of Toronto, Fall 2012, Slides 23-25 (multivariate CLT applied to multinomial data), <http://utstat.utoronto.ca/brunner/oldclass/appliedf12/lectures/2101f12RandomVectorsTwo.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
