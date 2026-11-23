# Split conformal coverage at the grid level

Let $n \in \mathbb{N}$, $\mu$ a probability measure on $\mathbb{R}^{n+1}$ (the law of the score vector) invariant under every coordinate permutation, $0 \le \alpha < 1$ and $k = \lceil (1 - \alpha)(n + 1) \rceil$. Then the test score is covered by the $k$-th smallest calibration score ($+\infty$ if $k > n$) with probability at least $k/(n + 1)$:

$$\mu\big(\omega_{n+1} \le \hat q_k(\omega)\big) \ge \frac{k}{n + 1}.$$

The proof applies validity of the permutation p-value at the grid level $(n + 1 - k)/(n + 1)$. The sources treat $0 < \alpha < 1$; the endpoint $\alpha = 0$ ($k = n + 1$, coverage $1$) is a trivial case.

## Sources

- V. Vovk, A. Gammerman and G. Shafer, *Algorithmic Learning in a Random World*, Springer, 2005.
- J. Lei, M. G'Sell, A. Rinaldo, R. J. Tibshirani and L. Wasserman, *Distribution-free predictive inference for regression*, J. Amer. Statist. Assoc. 113 (2018), 1094–1111.
