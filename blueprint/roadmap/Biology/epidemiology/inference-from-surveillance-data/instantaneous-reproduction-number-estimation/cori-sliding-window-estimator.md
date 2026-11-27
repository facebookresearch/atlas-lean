# Cori sliding-window estimator of the instantaneous reproduction number

Let $I_t$ be the incidence of infections (or cases) on day $t$ and let $w = (w_s)_{s \ge 1}$ be the serial-interval distribution, $w_s \ge 0$, $\sum_s w_s = 1$. Define the **total infectiousness** $\Lambda_t = \sum_{s \ge 1} w_s I_{t-s}$. Assume the renewal model

$$I_t \mid I_{t-1}, I_{t-2}, \dots \;\sim\; \mathrm{Poisson}(R_t \Lambda_t),$$

and that $R_t$ is constant, equal to $R$, on the window $W_t = \{t - \tau + 1, \dots, t\}$. With a $\mathrm{Gamma}(a, b)$ prior on $R$ (shape $a$, scale $b$), the posterior of $R$ given the incidence is

$$R \mid I \;\sim\; \mathrm{Gamma}\Bigl(a + \sum_{s \in W_t} I_s,\;\; \Bigl(\tfrac{1}{b} + \sum_{s \in W_t} \Lambda_s\Bigr)^{-1}\Bigr),$$

with posterior mean $\bigl(a + \sum_{W_t} I_s\bigr) / \bigl(1/b + \sum_{W_t} \Lambda_s\bigr)$ and posterior coefficient of variation $\bigl(a + \sum_{W_t} I_s\bigr)^{-1/2}$.

**Variant-specific application.** To compare co-circulating variants, split daily infections by variant before applying the estimator: given $S_i$ sequences on day $i$ with observed variant proportions $\pi_i$, draw $Y_i \sim \mathrm{Mult}(S_i, \pi_i)$ and set $P_i = Y_i / S_i$; given $I_i$ estimated infections, draw $Z_i \sim \mathrm{Mult}(I_i, P_i)$. Each bootstrap replicate of the variant series $Z_{i,v}$ yields an $R_t$ trajectory per variant, and ratios $R_t^{(v)} / R_t^{(v')}$ with bootstrap quantiles measure relative transmissibility.

## Proof depends on

- [Pooled Gamma–Poisson conjugacy](../../../../Probability/bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/pooled-posterior-eq-gamma-pdfreal.md)

## Expansion

On the window the likelihood is $\prod_{s \in W_t} (R \Lambda_s)^{I_s} e^{-R \Lambda_s} / I_s!$, proportional in $R$ to $R^{\sum I_s} e^{-R \sum \Lambda_s}$; multiplying by the Gamma prior density $\propto R^{a-1} e^{-R/b}$ gives the stated Gamma posterior (conjugacy). The window length $\tau$ trades bias for variance, and uncertainty in the serial interval is propagated by averaging the posterior over sampled serial-interval distributions. Because the posterior mean is pulled toward the prior mean $ab$ when $\sum I_s$ is small, a variant dying out produces spuriously rising estimates, so estimation starts only once cumulative incidence is large enough and is truncated at extinction. In the New England study, with a serial interval of mean 5.2 days and 21-day windows, Delta's mean $R_t$ was 1.63 to 2.67 times that of Alpha during co-circulation, depending on the state. The complementary growth-rate measure, $\exp(\beta \bar g)$ for logistic-regression slope $\beta$ and mean generation interval $\bar g$, is the logistic replacement advantage per generation.

## Sources

- R. Earnest, R. Uddin, N. Matluk, N. Renzette, S. E. Turbett, K. J. Siddle et al., "Comparative transmissibility of SARS-CoV-2 variants Delta and Alpha in New England, USA", Cell Reports Medicine (2022), 100583, STAR Methods "Growth rates and transmissibility estimation" (multinomial bootstrap and EpiEstim estimation), <https://doi.org/10.1016/j.xcrm.2022.100583>, PMCID PMC8913280.
- A. Cori, N. M. Ferguson, C. Fraser and S. Cauchemez, "A new framework and software to estimate time-varying reproduction numbers during epidemics", American Journal of Epidemiology 178 (2013), 1505–1512, <https://doi.org/10.1093/aje/kwt133>.
