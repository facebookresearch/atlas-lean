# Martingale CLT under the Lindeberg condition

On a probability space, let $X_{n,k}$ ($k < n$) be a triangular array such that for each $n$ the partial sums $\sum_{j<k} X_{n,j}$ form a martingale for a filtration $\mathcal F_n$, and each $X_{n,k}^2$ is integrable. Suppose the Lindeberg condition holds: for every $\varepsilon > 0$, $\sum_{k<n} \mathbb E\big[X_{n,k}^2 \mathbf 1\{|X_{n,k}| > \varepsilon\}\big] \to 0$, and suppose $\sum_{k<n} X_{n,k}^2 \to v$ in probability for a constant $v \ge 0$. Then $\sum_{k<n} X_{n,k}$ converges in distribution to $N(0, v)$.

## Sources

- McLeish (1974), remarks following Theorem (2.3), pp. 621–622 (the Lindeberg condition implies (a) and (b)); compare P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application* (1980), Theorem 3.2.
