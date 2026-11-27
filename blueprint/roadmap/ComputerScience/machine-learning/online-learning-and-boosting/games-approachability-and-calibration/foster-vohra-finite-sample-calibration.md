# Foster-Vohra forecaster: expected calibration error at most $1/(2K) + 2\sqrt{(K+1)/T}$

Fix $K \ge 1$ and forecasts on the grid $\{0, 1/K, \ldots, 1\}$. For a binary outcome sequence and forecasts $i_t/K$, the empirical $\ell_1$ calibration error is $C_T = \frac1T\sum_{k=0}^{K} \big|\sum_{t<T:\ i_t = k} (y_t - k/K)\big|$, the $\ell_1$ norm of the calibration vector $c_T \in \mathbb{R}^{K+1}$ with coordinates $c_T(k) = \frac1T\sum_{t<T:\ i_t = k} (y_t - k/K)$. There is an explicit randomized forecaster which in each round draws $i_t$ from a distribution $w_t$ supported on at most two adjacent grid points, computed from the current iterate of online gradient descent on the cube $[-1,1]^{K+1}$ run on the past expected payoffs (an approachability strategy for the $\ell_1$ ball of radius $1/(2K)$), such that against every adaptive adversary choosing $y_t$ from the past forecasts, the expected calibration vector $\bar c_T = \frac1T\sum_{t<T} u(w_t, y_t)$, where $u(w, y)_k = w(k)\,(y - k/K)$, satisfies

$$
\max\big(0,\ \|\bar c_T\|_1 - \tfrac{1}{2K}\big) = O\big(\sqrt{K/T}\big),
$$

and the forecaster spends $O(\log K)$ time per round on top of the gradient step.

## Proof sketch

Encode a round as the vector payoff $u(w_t, y_t)$; given the past, $c_T - \bar c_T$ is an average of martingale differences. Rounding to the nearest grid point puts $u$ in the $\ell_1$ ball of radius $1/(2K)$ for every outcome, which is the response condition. The $\ell_1$ distance to that ball equals $-\frac{1}{2K} - \min_{\|\theta\|_\infty \le 1}\langle -x, \theta\rangle$, so online gradient descent over the cube, together with a two-point distribution balancing the adjacent coordinates where the current iterate changes sign (which guarantees $\langle u(w, y), \theta\rangle \le \frac{1}{2K}$ for every $y$), bounds the distance of $\bar c_T$ by the average regret, $O(\sqrt{K/T})$.

Explicit constants (derived): the expected-distance form of Blackwell's theorem for payoffs of norm at most $1$, converted to $\ell_1$ by Cauchy-Schwarz over the $K+1$ coordinates, gives

1. $\mathbb{E}[C_T] \le \frac{1}{2K} + 2\sqrt{(K+1)/T}$;
2. $\Pr[C_T \ge \varepsilon] \le \frac{4(K+1)}{T(\varepsilon - 1/(2K))^2}$ whenever $\varepsilon > 1/(2K)$, by Markov's inequality on the squared distance.

Consequently, for all $\varepsilon, \delta > 0$ there are $K$ and $T_0 = O(K/(\delta\varepsilon^2))$ with $\mathbb{E}[C_T] \le \varepsilon$ and $\Pr[C_T \ge \varepsilon] \le \delta$ for all $T \ge T_0$; with $K \approx T^{1/3}$ the expected error is $O(T^{-1/3})$.

## Depends on

- [Asymptotic calibration](../../../../GameTheory/noncooperative-games/adaptive-heuristics/exists-calibrated-forecast.md)
- [Calibration score](../../../../GameTheory/noncooperative-games/adaptive-heuristics/calibration-score.md)

## Proof depends on

- [Blackwell's approachability theorem, expected-payoff form](../../../../GameTheory/noncooperative-games/blackwell-approachability/blackwell-expected-approachability.md)
- [Blackwell's characterization: response condition iff every containing halfspace is forceable](blackwell-response-halfspace-equivalence.md)

## Sources

- Dean P. Foster and Rakesh V. Vohra, "Asymptotic calibration", Biometrika 85(2), 1998.
- David Blackwell, "An analog of the minimax theorem for vector payoffs", Pacific Journal of Mathematics, 1956.
- J. Abernethy, P. L. Bartlett and E. Hazan, "Blackwell Approachability and No-Regret Learning are Equivalent", Proceedings of the 24th Annual Conference on Learning Theory (COLT), PMLR 19, 2011, Section 5, Lemma 20, Theorems 21 and 22, Algorithm 3.
