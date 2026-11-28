# Low-degree Bayesian estimation reaches the Kesten–Stigum threshold

Hopkins and Steurer's meta-algorithm computes the best low-degree polynomial approximation of posterior moments of the hidden parameters and recovers the parameters by robust tensor decomposition. Its meta-theorems (Theorems 1.1 and 1.3) need a correlated witness and bound circuit size, not running time: if $p(x, y)$ is a distribution over $x \in \{0,1\}^n$ and unit vectors $y$ with $p(x) \ge 2^{-n^{O(1)}}$ for every $x$, and a matrix-valued polynomial $P$ of degree $D$ satisfies $\mathbb{E}_{p(x,y)}\langle P(x), yy^\top\rangle \ge \delta\,(\mathbb{E}_{p(x)}\|P(x)\|_F^2)^{1/2}$, then for some $\delta' \ge \delta^{O(1)} > 0$ an estimator $\hat y(x)$ computed by a circuit of size $n^{O(D)}$ has $\mathbb{E}\langle \hat y(x), y\rangle^2 \ge \delta'$; the third-moment version takes exchangeable orthonormal $y_1, \dots, y_k$ and a tensor witness correlated with $\sum_i y_i^{\otimes 3}$, and outputs $n^{\mathrm{poly}(1/\delta)}$ unit vectors one of which correlates with a random $y_i$. Efficiency in the stochastic block model is a separate result. In the symmetric model with $k$ communities, within-community edge probability $a/n$ and across-community $b/n$, write $\varepsilon d = a - b$ and $k d = a + (k-1)b$; above the Kesten–Stigum threshold, that is when $\delta := 1 - k^2/(\varepsilon^2 d) > 0$, equivalently $(a-b)^2 > k\,(a + (k-1)b)$, self-avoiding-walk polynomials of degree $O(\log n)/\delta^{O(1)}$, evaluated by color coding, give an $n^{1/\mathrm{poly}(\delta)}$-time algorithm for weak recovery with correlation depending only on $\delta$, and the mixed-membership model with $k, \alpha, \varepsilon^2 d \le n^{o(1)}$ is handled the same way up to $\varepsilon^2 d > k^2(\alpha+1)^2$, the conjectured computational threshold. Below the threshold, for constants $d, \varepsilon, k, \delta$ with $\varepsilon^2 d < (1-\delta)k^2$ and distinct vertices $i, j$, every function $f$ of the graph with $\mathbb{E}_{G(n,d/n)} f = 0$ whose correlation $\mathbb{E}_{\mathrm{SBM}}[f(x)(\mathbf{1}[\sigma_i = \sigma_j] - 1/k)]$ with the pair label is at least a constant times $(\mathbb{E}_{G(n,d/n)} f^2)^{1/2}$ has degree at least $n^{c(d,\varepsilon,k)}$ for some $c(d,\varepsilon,k) > 0$ (Theorem 1.10). Under the low-degree heuristic this is evidence that recovery below the threshold requires time $\exp(n^{\Omega(1)})$, which matters when $k$ is large enough that recovery is information-theoretically possible there.

## Proof sketch

Self-avoiding walk counts between two vertices are unbiased low-degree estimators of their community correlation; their variance is controlled exactly when the branching factor times the squared second eigenvalue of the community matrix exceeds one, which is the Kesten–Stigum condition. Below the threshold, testing is not hard (triangle counts separate the block model from $G(n, d/n)$, and Theorem 1.9 only bounds the low-degree norm by $n^{o(1)}$ at degree $n^{o(1)}$), so the lower bound concerns estimation: a Fourier computation shows that no function of degree below $n^{c(d,\varepsilon,k)}$ correlates with the pair label in the sense above, which by the low-degree conjecture predicts subexponential hardness of recovery.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](low-degree-likelihood-ratio.md)

## Proof depends on

- [Low-degree conjecture](low-degree-conjecture.md)

## Sources

- S. B. Hopkins, D. Steurer, "Efficient Bayesian Estimation from Few Samples: Community Detection and Related Problems", FOCS (2017), arXiv:1710.00264.
