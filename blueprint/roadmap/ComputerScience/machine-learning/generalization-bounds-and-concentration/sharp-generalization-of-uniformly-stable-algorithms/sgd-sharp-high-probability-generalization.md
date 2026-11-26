# Sharp high-probability generalization of stochastic gradient descent on smooth convex losses

Let the loss $\ell(w, z)$ be convex, $\beta$-smooth and $L$-Lipschitz in $w$ and bounded by $B$. Projected stochastic gradient descent run for $T$ steps with step sizes $\eta_t \le 2/\beta$ is uniformly stable with parameter $\gamma = \frac{2L^2}{n}\sum_{t=1}^T \eta_t$ (Hardt, Recht and Singer). Consequently, with probability at least $1-\delta$, its output $w_T$ satisfies

$$
\big| R(w_T) - R_{\mathrm{emp}}(w_T) \big| \lesssim \frac{L^2 \sum_{t \le T} \eta_t}{n} \log n \log\frac{1}{\delta} + B\sqrt{\frac{\log(1/\delta)}{n}} .
$$

With $\eta_t = \eta$ and $T = n$ steps (one pass) this is $O\big((L^2 \eta \log n \log(1/\delta)) + B\sqrt{\log(1/\delta)/n}\big)$.

## Proof sketch

Run the two SGD trajectories on neighbouring samples with the same index sequence; for smooth convex losses and step size at most $2/\beta$ the gradient step is non-expansive, so the trajectories separate only when the differing example is sampled, by at most $2L\eta_t$, giving expected parameter distance $\frac{2L}{n}\sum_t \eta_t$ and hence stability $\gamma$ by Lipschitzness. Substituting $\gamma$ into the sharp stability bound gives the result.

## Depends on

- [Uniform stability](../algorithmic-stability/is-uniformly-stable.md)
- [Expected risk](../risk.md)
- [Empirical risk](../empirical-risk.md)

## Proof depends on

- [High-probability generalization of uniformly stable algorithms with a single logarithmic factor](uniform-stability-sharp-high-probability-bound.md)
- [SGM is uniformly stable](../algorithmic-stability/is-uniformly-stable-sgm.md)

## Sources

- M. Hardt, B. Recht, Y. Singer, "Train Faster, Generalize Better: Stability of Stochastic Gradient Descent", ICML (2016), arXiv:1509.01240.
- O. Bousquet, Y. Klochkov, N. Zhivotovskiy, "Sharper Bounds for Uniformly Stable Algorithms", COLT (2020), arXiv:1910.07833.
