# SIRD model with time-distributed recovery and death rates

In a closed population of size $N$ let $S, I, R, D$ be the numbers of susceptible, infected, recovered and dead individuals and $J(t) = \beta(t) S(t) I(t)/N$ the incidence. Let $r(s), d(s) \ge 0$ be the recovery and death rates at time since infection $s$, with $\int_0^\infty (r + d)\,ds \le 1$ (the fraction of an infection cohort that has recovered or died by time $s$ is $\int_0^s (r+d)$). The model is

$$\frac{dS}{dt} = -J(t), \quad \frac{dI}{dt} = J(t) - \int_0^t \bigl(r(t-\eta) + d(t-\eta)\bigr) J(\eta)\, d\eta, \quad \frac{dR}{dt} = \int_0^t r(t-\eta) J(\eta)\, d\eta, \quad \frac{dD}{dt} = \int_0^t d(t-\eta) J(\eta)\, d\eta,$$

with $S(0) = N - I_0$ (approximately $N$), $I(0) = I_0 > 0$, $R(0) = D(0) = 0$ and $J = 0$ for $t \le 0$, so that $I(t) = \int_0^t J - R(t) - D(t)$, up to the initial cases.

1. **Positivity.** $S, R, D \ge 0$ and $I(t) > 0$ for all $t > 0$.
2. **SIR limit.** If $r(s) = r_0$ and $d(s) = d_0$ for $0 \le s < \tau$ and $0$ afterwards (disease duration $\tau$), then $dI/dt = \beta S I/N - (r_0+d_0) I - (r_0+d_0)^2 \int_{t-\tau}^t \int_{s-\tau}^s J\, d\eta\, ds$. Neglecting the $O((r_0+d_0)^2)$ term gives the SIR model with deaths, $dI/dt = \beta SI/N - (r_0+d_0)I$, $dR/dt = r_0 I$, $dD/dt = d_0 I$.
3. **Transmission-rate inversion.** For a time-dependent transmission rate,

$$\beta(t) = \frac{N\, J(t)}{I(t)\,\bigl(N - \int_0^t J(\eta)\, d\eta\bigr)}, \tag{12}$$

so $\beta$ is determined by incidence, prevalence and cumulative incidence alone, whatever the kernels $r, d$.

## Expansion

For positivity, $S' = 0$ wherever $S = 0$, and $R, D$ are nondecreasing. Integrating $R' + D'$ and exchanging the order of integration gives $R(t_0) + D(t_0) = \int_0^{t_0} \bigl(\int_\eta^{t_0} (r + d)(t - \eta)\, dt\bigr) J(\eta)\, d\eta < \int_0^{t_0} J$, since the inner integral is the fraction of the cohort infected at $\eta$ that has left $I$ by $t_0$, which is less than $1$. For the SIR limit, a duration $\tau$ gives $I(t) = \int_{t-\tau}^t J - (r_0 + d_0)\int_{t-\tau}^t \int_{s-\tau}^s J$; substituting into $dI/dt$ isolates the quadratic correction. For (12), conservation gives $S = N - \int_0^t J$, which is substituted into $\beta = NJ/(SI)$. When cumulative incidence is small compared with $N$, $\beta \approx J/I$. With a fixed duration $\tau$ and exponential incidence $J \propto e^{\lambda t}$ this becomes $\beta = \lambda/(1 - e^{-\lambda\tau})$, which equals $1/\tau$ at $\lambda = 0$. Fitted to COVID-19 data, gamma-distributed $r$ and $d$ give a higher, earlier epidemic peak than the SIR model with the same mean duration, which recovers infecteds too early.

## Sources

- S. Ghosh, V. Volpert, M. Banerjee, "An epidemic model with time-distributed recovery and death rates", *Bulletin of Mathematical Biology* (2022), Section 2 (Eqs. (1)–(10): model, positiveness of solutions, reduction to the SIR model), Section 4 (comparison with the SIR model) and Section 6 (Theorem 1, Eq. (12)), <https://doi.org/10.1007/s11538-022-01028-0> (PMC9243747).
