# Conditional Granger causality of differenced series in time and frequency

**Setting.** Let $X_t, Y_t, Z_t$ be (possibly vector-valued) time series, for example expression levels of genes, and let $\Delta^k$ denote the $k$-th difference operator, $\Delta = 1 - L$ with lag operator $L$, so that $\Delta^k X_t$ is stationary when $X_t$ follows an ARIMA$(p,k,q)$ model. Fit two vector autoregressions by least squares (or as population linear projections):

- the joint model of $(\Delta^k X_t, \Delta^k Z_t)$ on their own pasts, with prediction error $\varepsilon_{1t}$ for the $X$ component;
- the joint model of $(\Delta^k X_t, \Delta^k Y_t, \Delta^k Z_t)$ on their own pasts, with prediction error $\varepsilon_{3t}$ for the $X$ component.

**Definition.** The conditional Granger causality from $Y$ to $X$ given $Z$ is

$$F_{Y \to X \mid Z} = \ln \frac{\operatorname{var}(\varepsilon_{1t})}{\operatorname{var}(\varepsilon_{3t})} .$$

**Properties.**
1. $F_{Y\to X\mid Z} \ge 0$, because the second model nests the first; $F_{Y\to X\mid Z} = 0$ iff the past of $Y$ does not improve the linear prediction of $X$ once the pasts of $X$ and $Z$ are known, in particular when the influence of $Y$ on $X$ is entirely mediated by $Z$ (all coefficients of past $Y$ in the $X$ equation vanish).
2. **Spectral decomposition.** After normalizing both models so that their noise covariance matrices become block diagonal and Fourier transforming, one obtains a frequency-resolved conditional causality $f_{Y\to X\mid Z}(\lambda)$, $\lambda \in [-\pi,\pi]$. The transfer functions of the differenced models differ from those of the corresponding ARMA models by the common factor $\Delta(\lambda,k)$, the Fourier transform of $\Delta^k$, which cancels; hence the ARIMA and ARMA formulations give the same frequency-domain causality.
3. **Kolmogorov identity.** Under the usual conditions for Geweke's decomposition, integrating the spectral measure over all frequencies returns the time-domain value, $F_{Y\to X\mid Z} = \frac{1}{2\pi}\int_{-\pi}^{\pi} f_{Y\to X\mid Z}(\lambda)\,d\lambda$.

## Expansion

Granger's notion is predictive: $Y$ causes $X$ if past $Y$ reduces the variance of the one-step prediction error of $X$. Pairwise analysis cannot distinguish direct from mediated influence, which motivates conditioning on $Z$: the ratio of residual variances compares the best predictions of $X$ with and without the past of $Y$, both already using the past of $Z$. Differencing removes polynomial trends and unit roots, so the measure applies to non-stationary expression series without changing which interactions are present. In practice the statistic is evaluated with bootstrap confidence intervals, and an interaction is declared when the interval excludes zero; the frequency-domain version reveals at which time scales an interaction acts.

## Sources

- C. Zou, C. Ladroue, S. Guo, J. Feng, "Identifying interactions in the time and frequency domains in local and global networks - A Granger Causality Approach", BMC Bioinformatics (2010), Methods: conditional Granger causality in the time domain (Eqs. (1)–(6)) and in the frequency domain (Eqs. (7)–(14)), <https://doi.org/10.1186/1471-2105-11-337>, PMCID PMC2897832.
