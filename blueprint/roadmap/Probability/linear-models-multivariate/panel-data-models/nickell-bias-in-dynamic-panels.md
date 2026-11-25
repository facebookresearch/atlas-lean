# Demeaning correlates the lagged regressor with the error in a short dynamic panel

Consider units $i = 1, 2, \dots$, i.i.d. across $i$, with $y_{i0} = \alpha_i + \varepsilon_{i0}$ and $y_{it} = \rho y_{i,t-1} + \alpha_i + \varepsilon_{it}$ for $t = 1, 2$, where $\rho = 0$, the $\varepsilon_{it}$ are i.i.d. with mean $0$ and variance $\sigma^2 > 0$, independent of $\alpha_i$, and $\alpha_i$ is square-integrable. Demean over $t \in \{1, 2\}$: $\tilde x_{it} = y_{i,t-1} - \tfrac12(y_{i0} + y_{i1})$ and $\tilde e_{it} = \varepsilon_{it} - \tfrac12(\varepsilon_{i1} + \varepsilon_{i2})$. Then $E[\sum_t \tilde x_{it}\tilde e_{it}] = -\sigma^2/2 \ne 0$ and $E[\sum_t \tilde x_{it}^2] = \sigma^2$, so the within estimator $\hat\rho_N = \sum_{i \le N}\sum_t \tilde x_{it}\tilde y_{it}/\sum_{i \le N}\sum_t \tilde x_{it}^2$, set to $0$ when the denominator is $0$ (an event that can have positive probability for finite $N$: $2^{-N}$ for Rademacher errors), converges almost surely to $-1/2$ as $N \to \infty$ instead of to $\rho = 0$: by the strong law the denominator is eventually positive. Nickell's general formula for the bias at fixed $T$ is a separate statement.

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md): cross-sectional averages of the i.i.d. unit-level sums.

## Sources

- M. Arellano, *Time series and panel data econometrics*, class notes, CEMFI, section "The Nickell bias", equations (85)–(88), <https://www.cemfi.es/~arellano/time-series-panels-class-note.pdf>
