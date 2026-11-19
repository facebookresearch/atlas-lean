# Uniform stability of SGM for convex, smooth, Lipschitz losses

Let every loss $\ell(\cdot, z)$ be convex, differentiable and $L$-Lipschitz on a real Hilbert space, with $\beta$-Lipschitz gradient ($\beta > 0$), and let the steps satisfy $0 \le \alpha_t \le 2/\beta$. Let $S$ and $S'$ be samples of size $n \ge 1$ that differ in one example, and let $w_T$ and $w'_T$ be the outputs of $T$ steps of the stochastic gradient method from the same $w_0$, with the same indices drawn by the [random selection rule](index-measure.md). Then for every test example $z$,

$$
\mathbb{E}\, \big\lvert \ell(w_T, z) - \ell(w'_T, z) \big\rvert \le \frac{2 L^2}{n} \sum_{t=0}^{T-1} \alpha_t .
$$

Proof: since $\ell(\cdot, z)$ is $L$-Lipschitz, the left side is at most $L\, \mathbb{E}\lVert w_T - w'_T\rVert$. Along each index sequence the [coupled distance](norm-sgm-iterate-sub-le.md) is at most $\sum_t 2\alpha_t L \cdot \mathbf{1}[\text{step } t \text{ selects the differing example}]$, and each step selects it with probability $1/n$.

The bound does not depend on the number of passes over the data, only on the total step length $\sum_t \alpha_t$: SGD that is stopped early, or run with decreasing steps, is stable. Combined with [the generalization bound for stable algorithms](abs-integral-empirical-risk-sub-risk-le.md), this gives the [generalization bound for SGM](abs-integral-empirical-risk-sub-risk-sgm.md), for a loss bounded at the starting point, the "train faster, generalize better" principle. It complements the optimization rate of [stochastic gradient descent](../../../../Analysis/convex-analysis-and-variations/gradient-descent/integral-sgd-average-sub-le.md): the optimization error decreases and the stability bound increases with $\sum_t \alpha_t$.

The source states the theorem for steps $\alpha_t > 0$ indexed from $1$ to $T$; here the steps are indexed from $0$ and may vanish. Its strongly convex (Theorem 3.9) and non-convex (Theorem 3.12) versions are not treated here.

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Theorem 3.8 (inequality (3.3) and the recursion (3.4), unrolled).
