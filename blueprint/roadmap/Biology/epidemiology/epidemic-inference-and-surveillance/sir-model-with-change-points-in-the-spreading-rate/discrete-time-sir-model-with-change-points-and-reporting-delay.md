# Discrete-time SIR model with change points and a reporting delay

**Base model.** In a closed population of size $N$, susceptible ($S$), infected ($I$) and recovered ($R$) compartments follow the SIR equations with spreading rate $\lambda > 0$ and recovery rate $\mu > 0$,

$$\frac{dS}{dt} = -\lambda \frac{S I}{N}, \qquad \frac{dI}{dt} = \lambda \frac{S I}{N} - \mu I, \qquad \frac{dR}{dt} = \mu I .$$

With a time step $\Delta t$ (one day) this is discretized as

$$I^{\mathrm{new}}_t = \lambda \Delta t \, \frac{S_{t-1}}{N} I_{t-1}, \qquad R^{\mathrm{new}}_t = \mu \Delta t \, I_{t-1},$$

$$S_t = S_{t-1} - I^{\mathrm{new}}_t, \qquad R_t = R_{t-1} + R^{\mathrm{new}}_t, \qquad I_t = I_{t-1} + I^{\mathrm{new}}_t - R^{\mathrm{new}}_t ,$$

started at $t = 0$ from $I_0$ infected people. $I_t$ counts currently active infections, $I^{\mathrm{new}}_t$ new infections.

**Reporting delay.** New infections are reported after a delay of $D \ge 0$ days, so the modelled number of newly reported cases is $C_t = I^{\mathrm{new}}_{t-D}$. A weekly reporting modulation multiplies this by $1 - f(t)$ with

$$f(t) = (1 - f_w)\left(1 - \left|\sin\!\left(\tfrac{\pi}{7} t - \tfrac{1}{2}\Phi_w\right)\right|\right),$$

where $f_w \in [0, 1]$ and the phase $\Phi_w$ are estimated.

**Change points.** The spreading rate is piecewise linear in time: given change-point times $t_1 < \dots < t_n$, durations $\Delta t_i > 0$ and rates $\lambda_0, \lambda_1, \dots, \lambda_n$, the rate equals $\lambda_{i-1}$ before $t_i$, moves linearly from $\lambda_{i-1}$ to $\lambda_i$ over a window of length $\Delta t_i$ around $t_i$, and equals $\lambda_i$ afterwards (until the next change point). The discrete recursion above is run with this time-varying $\lambda$.

**Observation model.** Given observed daily reports $\hat C_t$ and parameters $\theta = \{\lambda_i, t_i, \Delta t_i, \mu, D, \sigma, I_0, f_w, \Phi_w\}$, the local likelihoods are independent Student-$t$ densities with $\nu = 4$ degrees of freedom,

$$\hat C_t \mid \theta \sim \mathrm{StudentT}_{\nu = 4}\!\left(\text{location } C_t(\theta),\ \text{scale } \sigma \sqrt{C_t(\theta)}\right),$$

so that the variance grows proportionally to the modelled mean (as for random subsampling of cases), while the heavy tails limit the influence of reporting outliers. The posterior is $p(\theta \mid \hat C) \propto \prod_t p(\hat C_t \mid \theta) \, p(\theta)$.

Properties:

- with a single regime ($n = 0$) and $S \approx N$, the active infections grow as $I(t) = I(0) e^{(\lambda - \mu) t}$, so the sign of the effective growth rate $\lambda^* = \lambda - \mu$ separates supercritical ($\lambda > \mu$) from subcritical ($\lambda < \mu$) spread;
- after a change point that brings $\lambda$ below $\mu$, reported cases keep following the old regime for $D$ days before turning, because $C_t$ reads infections $D$ days in the past;
- an abrupt change (small $\Delta t_i$) can produce a transient dip in daily new cases even when $\lambda > \mu$ at all times, while gradual ramps centred on the same day give similar case curves.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

The discrete update is the forward Euler step of the SIR system with $\Delta t = 1$ day; the only data-facing quantities are the delayed new infections $C_t$, which is why the delay $D$ and the change-point times $t_i$ are partially confounded and must be estimated jointly. The exponential approximation in the first property follows by setting $S/N = 1$ in the $I$ equation, which becomes linear. Posterior sampling uses gradient-based Markov chain Monte Carlo (No-U-Turn sampling) initialized by variational inference, with convergence checked by the rank-normalized $\hat R < 1.05$; forecasts are obtained by continuing the recursion from every posterior sample under each intervention scenario.

## Sources

- J. Dehning, J. Zierenberg, F. P. Spitzner, M. Wibral, J. P. Neto, M. Wilczek and V. Priesemann, "Inferring change points in the spread of COVID-19 reveals the effectiveness of interventions", Science 369 (2020), eabb9789, Materials and Methods, Eqs. (1)–(5) and the likelihood specification, <https://doi.org/10.1126/science.abb9789> (PMC7239331).
