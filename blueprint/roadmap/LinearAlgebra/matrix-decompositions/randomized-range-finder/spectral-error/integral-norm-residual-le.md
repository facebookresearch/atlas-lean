# Average spectral error of the randomized range finder

Under the hypotheses of the Frobenius bound (real $m \times n$ matrix $A$, $k \ge 2$, $p \ge 2$, $k + p \le \min\{m,n\}$, $\Omega$ an $n \times (k+p)$ standard Gaussian matrix, $Y = A\Omega$),

$$\mathbb{E}\,\|(I - P_Y)A\| \le \left(1 + \sqrt{\frac{k}{p-1}}\right)\sigma_{k+1} + \frac{e\sqrt{k+p}}{p}\Big(\sum_{j>k}\sigma_j^2\Big)^{1/2},$$

where $\|\cdot\|$ is the spectral norm. Here $\sigma_1 \ge \sigma_2 \ge \cdots$ are the singular values of $A$, indexed from $1$. The first term is comparable with the optimal rank-$k$ spectral error $\sigma_{k+1}$. The second term is the price of the spectral norm, and becomes small when the singular values decay.

## Background

- [Eckart–Young theorem in operator norm](../../../../Analysis/operator-theory/eigenvalue-inequalities/eckart-young-best-rank-approx-operator-n.md): background, the best rank-$k$ error $\sigma_{k+1}$ (indexed from $0$ there as $\sigma_k$) that serves as the benchmark.
- [Real singular value decomposition](../../singular-value-decomposition/singular-value-decomposition-theorem/real-singular-value-decomposition.md): background, the singular values $\sigma_j$ used in the bound.

## Sources

- N. Halko, P.-G. Martinsson and J. A. Tropp, Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions, SIAM Rev. 53 (2011), 217–288, arXiv:0909.4061, Theorem 10.6.
