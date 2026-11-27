# Deterministic forecasters have calibration error at least 1/2 against an adaptive adversary

Let $f$ map each finite binary history to a forecast in $\mathbb{R}$. Against the adaptive adversary that sets the outcome $y_t = 1$ if $f(y_0,\ldots,y_{t-1}) < 1/2$ and $y_t = 0$ otherwise, for every horizon $T \ge 1$ the bucketed $\ell_1$ calibration error

$$
C_T = \frac1T \sum_{r} \Big| \sum_{t<T:\ f_t = r} (y_t - r) \Big|
$$

(summing over the distinct forecast values $r$ used) is at least $1/2$. Hence randomization is necessary for asymptotic calibration.

## Proof sketch

Every round contributes a signed error $y_t - f_t$ of absolute value at least $1/2$ whose sign is fixed by the bucket: forecasts below $1/2$ always see outcome $1$ and forecasts at least $1/2$ always see outcome $0$. So within each bucket the errors do not cancel, and the total is at least $T/2$.

## Depends on

- [Calibration score](../../../../GameTheory/noncooperative-games/adaptive-heuristics/calibration-score.md)

## Sources

- Dean P. Foster and Rakesh V. Vohra, "Asymptotic calibration", Biometrika 85(2), 1998.
