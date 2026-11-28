# Serfling cyclic regression baseline for excess mortality

**Model.** Let $y(t)$ be a surveillance count (for example weekly deaths attributed to pneumonia and influenza) observed at times $t = 1, 2, \dots$ with seasonal period $P$ (52 for weekly data, 13 for four-week periods). The Serfling model fits, to epidemic-free periods, the cyclic regression

$$y(t) = \theta_0 + \theta_1 t + \sum_{k=1}^{K}\Big[\gamma_k \cos\!\Big(\frac{2\pi k t}{P}\Big) + \delta_k \sin\!\Big(\frac{2\pi k t}{P}\Big)\Big] + e(t),$$

with $e(t)$ independent $\mathcal{N}(0, \sigma^2)$ errors, usually $K = 1$ (one annual harmonic) and optionally a quadratic trend term $\theta_2 t^2$. The parameters are estimated by ordinary least squares.

**Detection rule.** With fitted baseline $\hat\mu(t)$ and residual standard deviation $\hat\sigma$, an alert is raised at time $t$ when

$$y(t) > \hat\mu(t) + z_{1-\alpha}\, \hat\sigma,$$

typically with a one-sided 95% threshold ($z_{0.95} \approx 1.645$). The excess over the baseline during alert periods, $\sum_t (y(t) - \hat\mu(t))_+$, is the estimated epidemic-attributable count.

**Properties.**

1. Because $\cos$ and $\sin$ of the same frequency combine as $\gamma\cos\omega t + \delta\sin\omega t = A\cos(\omega t - \phi)$ with $A = \sqrt{\gamma^2 + \delta^2}$ and $\tan\phi = \delta/\gamma$, the model is linear in its parameters while fitting a seasonal wave of free amplitude and phase.
2. Under the Gaussian model, the threshold rule has false-alarm probability $\alpha$ per time point during non-epidemic periods, ignoring estimation error in $\hat\mu$ and $\hat\sigma$.
3. Serial correlation in $e(t)$ (which the model ignores) inflates the false-alarm rate, which motivates autoregressive (ARIMA/SARIMA) alternatives.

## Expansion

The baseline must be fitted on data excluding epidemic periods, otherwise epidemic peaks inflate both the seasonal amplitude and $\hat\sigma$ and mask excess. The amplitude–phase identity follows from the angle-difference formula for cosine. The rule in property 2 is a pointwise test; the overall number of false alarms over a season scales with the number of time points, so operational systems often require several consecutive exceedances. The approach is used by national public-health agencies for influenza and, with additional covariates, for all-cause excess-mortality estimation.

## Sources

- Siettos CI, Russo L, "Mathematical modeling of infectious disease dynamics" (2013), section "Statistical-Based Methods for Epidemic Surveillance", regression methods (Serfling cyclic regression and threshold alerting), <https://doi.org/10.4161/viru.24041>, PMCID PMC3710332.
- R. E. Serfling, "Methods for current statistical analysis of excess pneumonia-influenza deaths", Public Health Reports 78 (1963) 494–506.
