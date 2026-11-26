# FIR ridge estimation of time-varying transmission and recovery rates in the SIR model

**Setting.** In the discrete-time SIR model with time-varying rates, with population fractions $s, i, r$ ($s + i + r \approx 1$) and daily step,

$$s(t+1) - s(t) = -\beta(t)s(t)i(t), \qquad i(t+1) - i(t) = \beta(t)s(t)i(t) - \gamma(t)i(t), \qquad r(t+1) - r(t) = \gamma(t)i(t),$$

the rates are recovered exactly from consecutive observations of $i$ and $r$:

$$\gamma(t) = \frac{r(t+1) - r(t)}{i(t)}, \qquad \beta(t) = \frac{[i(t+1) - i(t)] + [r(t+1) - r(t)]}{i(t)\,[1 - i(t) - r(t)]}, \qquad 0 \le t \le T-2 .$$

**Proposition (deaths can be merged into removals).** If deaths $d$ form a separate compartment with rate $\delta(t) = (d(t+1) - d(t))/i(t)$, then with $\tilde r = r + d$ and $\tilde\gamma = \gamma + \delta$ the SIRD system reduces to the SIR system above, and the same formula for $\beta(t)$ holds with $r$ replaced by $\tilde r$; the transmission-rate estimate is unchanged by whether deaths are counted as removals.

**Proposition (FIR models as ridge regression).** Model the rates as finite-impulse-response (autoregressive) filters of orders $J$ and $K$,

$$\hat\beta(t) = a_0 + \sum_{j=1}^J a_j\,\beta(t-j), \qquad \hat\gamma(t) = b_0 + \sum_{k=1}^K b_k\,\gamma(t-k),$$

fitted by penalised least squares $\min_a \sum_{t=J}^{T-2}(\beta(t) - \hat\beta(t))^2 + \alpha_1\sum_{j=0}^J a_j^2$ and likewise for $b$ with penalty $\alpha_2$. These problems are equivalent to the ridge regressions

$$\min_{a}\ \|y - Xa\|^2 + \alpha_1\|a\|^2, \qquad \min_{b}\ \|z - Yb\|^2 + \alpha_2\|b\|^2,$$

with $y \in \mathbb{R}^{T-J-1}$, $X \in \mathbb{R}^{(T-J-1)\times(J+1)}$ the matrix whose rows are $(1, \beta(t-1), \dots, \beta(t-J))$, and analogously for $z, Y$; hence $a^{ridge} = (X^\top X + \alpha_1 I)^{-1}X^\top y$ and $b^{ridge} = (Y^\top Y + \alpha_2 I)^{-1}Y^\top z$.

**Forecasting.** Predictions over a window $T \le t \le T+W$ iterate $\hat\beta, \hat\gamma$ and

$$i(t+1) = \big[1 + \beta(t)(1 - i(t) - r(t)) - \gamma(t)\big]i(t), \qquad r(t+1) = r(t) + \gamma(t)i(t).$$

The modified algorithm re-solves both ridge problems at every forecast step ($T \gets T+1$), including the newly predicted rates, instead of reusing the coefficients fitted once on the training window.

## Expansion

Adding the infected and removed increments eliminates $\gamma$ and isolates the new infections $\beta s i$, and $s = 1 - i - r$ closes the formula for $\beta$, so the time-varying model is fully identifiable from daily counts. Treating $\beta(t)$ and $\gamma(t)$ as outputs of a linear FIR system with memory $J$ or $K$ turns forecasting into a small regression; the ridge penalty stabilises it when the lagged rates are strongly collinear, as they are for smoothly varying epidemics. Re-fitting at each step lets the filter coefficients adapt to the trend of the rates within the prediction window, at the price of feeding its own predictions back into the fit.

## Sources

- Felipe Rogério Pimentel, Rafael Gustavo Alves, "Modification of a Numerical Method Using FIR Filters in a Time-dependent SIR Model for COVID-19", arXiv:2506.21739 (2025), Section 2 (time-dependent SIR model and rate formulas), Section 3 (equivalence between models), Section 4 (FIR estimation, Proposition 1, Algorithm 1) and Section 5 (modification of Algorithm 1), <https://doi.org/10.48550/arXiv.2506.21739>.
