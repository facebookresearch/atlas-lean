# Split conformal coverage as a permutation test

Let $n \in \mathbb{N}$, $\alpha < 1$, $k = \lceil (1 - \alpha)(n + 1) \rceil$ and $\omega \in \mathbb{R}^{n+1}$. The test score is covered by the threshold $\hat q_k(\omega)$ (the $k$-th smallest calibration score, or $+\infty$ if $k > n$) if and only if the [permutation p-value](permutation-pvalue-eval-last.md) of the test coordinate exceeds $\alpha$. Ties are allowed.
