# Foster-Vohra forecaster: expected calibration error at most $1/(2K) + 2\sqrt{(K+1)/T}$

Fix $K \ge 1$ and forecasts on the grid $\{0, 1/K, \ldots, 1\}$. For a binary outcome sequence and forecasts $i_t/K$, the empirical $\ell_1$ calibration error is $C_T = \frac1T\sum_{k=0}^{K} \big|\sum_{t<T:\ i_t = k} (y_t - k/K)\big|$. There is an explicit randomized forecaster, which in each round plays a distribution supported on at most two adjacent grid points chosen from the current cumulative calibration vector (a Blackwell approachability strategy for the $\ell_1$ ball of radius $1/(2K)$), such that against every adaptive adversary choosing $y_t$ from the past forecasts, for every $T \ge 1$:

1. $\mathbb{E}[C_T] \le \frac{1}{2K} + 2\sqrt{(K+1)/T}$;
2. $\Pr[C_T \ge \varepsilon] \le \frac{4(K+1)}{T(\varepsilon - 1/(2K))^2}$ whenever $\varepsilon > 1/(2K)$.

Consequently, for all $\varepsilon, \delta > 0$ there are $K$ and $T_0 = O(K/(\delta\varepsilon^2))$ with $\mathbb{E}[C_T] \le \varepsilon$ and $\Pr[C_T \ge \varepsilon] \le \delta$ for all $T \ge T_0$; with $K \approx T^{1/3}$ the expected error is $O(T^{-1/3})$.

## Proof sketch

Encode a round as the vector payoff $(y - i/K)e_i \in \mathbb{R}^{K+1}$, whose running average has $\ell_1$ norm equal to $C_T$. Rounding to the nearest grid point verifies the response condition for the $\ell_1$ ball of radius $1/(2K)$; an explicit two-point distribution balancing adjacent coordinates of the current residual satisfies the halfspace condition. The expected-distance Blackwell bound in Euclidean norm, converted to $\ell_1$ by Cauchy-Schwarz over $K+1$ coordinates, gives item 1, and Markov's inequality on the squared distance gives item 2.

## Depends on

- [Asymptotic calibration](../../../../GameTheory/noncooperative-games/adaptive-heuristics/exists-calibrated-forecast.md)
- [Calibration score](../../../../GameTheory/noncooperative-games/adaptive-heuristics/calibration-score.md)

## Proof depends on

- [Blackwell's approachability theorem, expected-payoff form](../../../../GameTheory/noncooperative-games/blackwell-approachability/blackwell-expected-approachability.md)
- [Blackwell's characterization: response condition iff every containing halfspace is forceable](blackwell-response-halfspace-equivalence.md)

## Sources

- Dean P. Foster and Rakesh V. Vohra, "Asymptotic calibration", Biometrika 85(2), 1998.
- David Blackwell, "An analog of the minimax theorem for vector payoffs", Pacific Journal of Mathematics, 1956.
