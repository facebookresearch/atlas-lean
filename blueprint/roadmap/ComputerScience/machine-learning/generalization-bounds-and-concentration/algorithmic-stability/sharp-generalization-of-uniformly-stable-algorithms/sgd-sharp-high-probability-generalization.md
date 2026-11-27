# Sharp high-probability generalization of stochastic gradient descent on smooth convex losses

Let the loss $\ell(w, z)$ be convex, $\beta$-smooth and $L$-Lipschitz in $w$ and bounded by $B$. Run projected stochastic gradient descent for $T$ steps with step sizes $\eta_t \le 2/\beta$, choosing the example of each step uniformly at random, and write $w_T$ for its output on the sample $S$ of $n$ examples. Hardt, Recht and Singer (Definition 2.1 and Theorem 3.8) show that SGD is uniformly stable *in expectation over its internal randomness*: the deterministic averaged loss

$$
g_S(z) = \mathbb{E}_{\mathrm{SGD}}\big[\ell(w_T, z) \mid S\big]
$$

changes by at most $\gamma = \frac{2L^2}{n}\sum_{t=1}^T \eta_t$ at every $z$ when one example of $S$ is replaced. Consequently, for every $\delta \in (0,1)$, with probability at least $1-\delta$ over $S$,

$$
\Big| \mathbb{E}_{z}\big[g_S(z)\big] - \frac{1}{n}\sum_{i=1}^n g_S(z_i) \Big| \lesssim \frac{L^2 \sum_{t \le T} \eta_t}{n} \log n \log\frac{e}{\delta} + B\sqrt{\frac{\log(e/\delta)}{n}} ,
$$

that is, the generalization gap $\mathbb{E}_{\mathrm{SGD}}[R(w_T) - R_{\mathrm{emp}}(w_T) \mid S]$ averaged over SGD's randomness satisfies this bound. Logarithms of the confidence parameter are floored at $1$, as in the sharp stability bound. With $\eta_t = \eta$ and $T = n$ steps (one pass) the right-hand side is $O\big(L^2 \eta \log n \log(e/\delta) + B\sqrt{\log(e/\delta)/n}\big)$. The statement does not bound the gap of a single realised output $w_T$; that would need additional control of SGD's internal randomness.

## Proof sketch

Run the two SGD trajectories on neighbouring samples with the same index sequence; for smooth convex losses and step size at most $2/\beta$ the gradient step is non-expansive, so the trajectories separate only when the differing example is sampled, by at most $2L\eta_t$, giving expected parameter distance at most $\frac{2L}{n}\sum_t \eta_t$ over the index sequence. By Lipschitzness, $|g_S(z) - g_{S'}(z)| \le \gamma$ for all $z$, so the deterministic map $S \mapsto g_S$ is $\gamma$-uniformly stable with values bounded by $B$. Applying the sharp stability bound to $g_S$, with probability over $S$ only, gives the result.

## Depends on

- [Uniform stability](../is-uniformly-stable.md)
- [Expected risk](../../risk.md)
- [Empirical risk](../../empirical-risk.md)

## Proof depends on

- [High-probability generalization of uniformly stable algorithms with a single logarithmic factor](uniform-stability-sharp-high-probability-bound.md)
- [SGM is uniformly stable](../is-uniformly-stable-sgm.md)

## Sources

- M. Hardt, B. Recht, Y. Singer, "Train Faster, Generalize Better: Stability of Stochastic Gradient Descent", ICML (2016), arXiv:1509.01240.
- O. Bousquet, Y. Klochkov, N. Zhivotovskiy, "Sharper Bounds for Uniformly Stable Algorithms", COLT (2020), arXiv:1910.07833.
