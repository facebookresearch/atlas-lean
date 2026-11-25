# Effective rank $R_k$

For a real sequence $\lambda_1, \lambda_2, \dots$ (the eigenvalues of a covariance operator $\Sigma$) and $k \in \mathbb{N}$,

$$R_k(\Sigma) = \frac{\big(\sum_{i > k} \lambda_i\big)^2}{\sum_{i > k} \lambda_i^2},$$

where a series that does not converge (absolutely) is taken to be $0$ and a quotient by $0$ is $0$.

In Bartlett, Long, Lugosi and Tsigler's Theorem 4 the variance part of the excess risk of the minimum-norm interpolant is of order $k^*/n + n / R_{k^*}(\Sigma)$, where $k^*$ is the first $k$ with $r_k(\Sigma) \ge b n$. A large $R_{k^*}(\Sigma)$ compared with $n$ makes the
contribution $n / R_{k^*}(\Sigma)$ small; their sufficient criterion for a benign covariance sequence also
requires $k^*/n$ and $r_0(\Sigma)/n$ to tend to $0$ (Section 3.1).

## Sources

- P. L. Bartlett, P. M. Long, G. Lugosi and A. Tsigler, *Benign overfitting in linear regression*, Proceedings of the National Academy of Sciences 117 (2020) 30063–30070; arXiv:1906.11300 (v3), Definition 3 and Theorem 4.
