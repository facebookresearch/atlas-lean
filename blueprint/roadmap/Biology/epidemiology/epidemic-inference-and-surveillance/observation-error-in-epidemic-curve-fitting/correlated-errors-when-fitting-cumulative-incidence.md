# Correlated errors when fitting cumulative incidence

**Transmission and observation model.** Consider an SEIR model in a population of constant size $N$ whose latent period is split into $m$ stages $E_1, \dots, E_m$, each left at rate $m\alpha$ (so the incubation period is Erlang with mean $1/\alpha$ and shape $m$), with infectious period of mean $1/\gamma$ and force of infection

$$\lambda(t) = R_0\,\gamma\, \frac{I(t)}{N}.$$

Let $\Delta N_{E \to I}(t_1, t_2)$ be the number of transitions $E_m \to I$ in $(t_1, t_2]$. For a reporting period $\Delta t$, the true number of new infectious cases is $H_t = \Delta N_{E \to I}(t - \Delta t, t)$, and the reported count is

$$C_t \sim \mathrm{NegBin}\big(\text{mean } \rho H_t,\ \text{size } 1/k\big), \qquad \mathbb{E}[C_t \mid H_t] = \rho H_t, \quad \mathrm{Var}[C_t \mid H_t] = \rho H_t + k\,(\rho H_t)^2,$$

with reporting probability $\rho$ and reporting overdispersion $k \ge 0$. Fitting to cumulative data instead replaces $H_t$ by $\Delta N_{E \to I}(0, t)$.

**Statement (accumulated errors are dependent).** Let $Y_1, Y_2, \dots$ be the per-period count errors (observation minus model prediction), assumed independent with variances $v_s > 0$, and let $Z_t = \sum_{s \le t} Y_s$ be the corresponding errors of cumulative counts. Then for $s < t$

$$\mathrm{Cov}(Z_s, Z_t) = \mathrm{Var}(Z_s) = \sum_{u \le s} v_u, \qquad \mathrm{Corr}(Z_s, Z_t) = \sqrt{\frac{\sum_{u \le s} v_u}{\sum_{u \le t} v_u}},$$

so consecutive cumulative errors are strongly positively correlated (for constant $v_u$, $\mathrm{Corr}(Z_{t-1}, Z_t) = \sqrt{(t-1)/t} \to 1$) and their variance grows linearly in $t$. A least-squares or likelihood fit that treats the $Z_t$ as independent, identically distributed errors therefore uses a misspecified error model: it counts each per-period deviation many times, which yields overconfident (too narrow) uncertainty for $R_0$ and other parameters and hides lack of fit.

## Expansion

The covariance identity is bilinearity: $\mathrm{Cov}(Z_s, Z_t) = \sum_{u \le s}\sum_{w \le t}\mathrm{Cov}(Y_u, Y_w) = \sum_{u \le s} v_u$ because only the diagonal terms $u = w \le s$ survive. The negative-binomial moments follow from the gamma–Poisson mixture with shape $1/k$. The Erlang incubation period is the method of stages: the sum of $m$ independent exponential sojourns of rate $m\alpha$. In the source, deterministic models were fitted by least squares to stochastically simulated cumulative incidence and recovered biased $R_0$ with confidence intervals that frequently excluded the truth; fitting the stochastic model with the negative-binomial observation process to raw (non-accumulated) weekly counts reduced bias, quantified forecast uncertainty properly, and exposed misfit through diagnostics such as the lag-one autocorrelation of weekly cases.

## Sources

- A. A. King, M. Domenech de Cellès, F. M. G. Magpantay, P. Rohani, "Avoidable errors in the modelling of outbreaks of emerging pathogens, with special reference to Ebola", Proceedings of the Royal Society B (2015), Section 2 (deterministic models fit to cumulative incidence) and Section 5(b) (model formulation and negative-binomial observation model), <https://doi.org/10.1098/rspb.2015.0347> (PMC4426634).
