# Deterministic forecasters have calibration error at least 1/2 against an adaptive adversary

Let $f$ be a deterministic forecasting rule that maps each finite binary history to a probability forecast in $[0,1]$. Against the adaptive adversary that sets the outcome $X_t = 1$ if the forecast $f_t = f(X_1, \ldots, X_{t-1})$ for round $t$ is at most $0.5$ and $X_t = 0$ otherwise, the calibration score after $t$ rounds

$$
C_t = \sum_{p} \big(\rho_t(p) - p\big)^2\,\frac{n_t(p)}{t}
$$

(summing over the distinct forecast values $p$ used in the first $t$ rounds, where $n_t(p)$ is the number of those rounds with forecast $p$ and $\rho_t(p)$ the fraction of them with outcome $1$) satisfies $C_t \ge 1/4$ for every $t \ge 1$, with equality exactly when every forecast is $1/2$. Hence randomization is necessary for asymptotic calibration.

## Proof sketch

A forecast value $p \le 1/2$ is always followed by outcome $1$, so $\rho_t(p) = 1$ and $(\rho_t(p) - p)^2 = (1-p)^2 \ge 1/4$, with equality only at $p = 1/2$; a forecast value $p > 1/2$ is always followed by outcome $0$, so $(\rho_t(p) - p)^2 = p^2 > 1/4$. The weights $n_t(p)/t$ sum to $1$, so $C_t \ge 1/4$.

The same adversary also defeats the bucketed $\ell_1$ calibration error. For forecasts in $\mathbb{R}$ and the adversary setting $y_t = 1$ if $f_t < 1/2$ and $y_t = 0$ otherwise, every horizon $T \ge 1$ has

$$
\frac1T \sum_{r} \Big| \sum_{t \le T:\ f_t = r} (y_t - r) \Big| \ge \frac12,
$$

summing over the distinct forecast values $r$ used: every round contributes a signed error $y_t - f_t$ of absolute value at least $1/2$ whose sign is fixed by its bucket (forecasts below $1/2$ always see outcome $1$, forecasts at least $1/2$ always see outcome $0$), so within each bucket the errors do not cancel and the total is at least $T/2$.

## Depends on

- [Calibration score](../../../../GameTheory/noncooperative-games/adaptive-heuristics/calibration-score.md)

## Sources

- Dean P. Foster and Rakesh V. Vohra, "Asymptotic calibration", Biometrika 85(2), 1998, Sections 2 and 3.
