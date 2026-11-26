# HawkesN process and the dimensionless SIR model

In a population of size $N$, the HawkesN process modulates the self-exciting intensity by the fraction of individuals not yet infected:

$$\lambda_h(t) = \left(1 - \frac{I_c(t)}{N}\right)\left(\mu + \sum_{t_i < t} R(t_i)\, w(t - t_i)\right), \tag{5}$$

where $I_c(t)$ is the cumulative number of infections before $t$. Its deterministic counterpart is the SIR model

$$\frac{dS}{dt} = -\beta \frac{I S}{N}, \qquad \frac{dI}{dt} = \beta\frac{I S}{N} - \gamma I, \qquad \frac{dR}{dt} = \gamma I, \tag{6}$$

with $R_0 = \beta / \gamma$. Rescaling time by $\tau = \gamma t$ and writing $s = S/N$, $i = I/N$, $r = R/N$ gives, for a novel outbreak,

$$\frac{ds}{d\tau} = -R_0\, i s, \qquad \frac{di}{d\tau} = R_0\, i s - i, \qquad \frac{dr}{d\tau} = i, \qquad (s, i, r)\big|_{\tau = 0} = (1 - \epsilon, \epsilon, 0), \tag{7}$$

with $0 < \epsilon \ll 1$.

Properties:

- $\lambda_h(t) = 0$ once $I_c(t) = N$, so HawkesN produces at most $N$ infections; for $I_c \ll N$ it reduces to the Hawkes process (1);
- in (7) the trajectory is determined by the single parameter $R_0$ and the seed $\epsilon$; $\gamma$ only sets the time scale, so the timing and size of the peak in $\tau$ depend on $R_0$ alone (up to the seed);
- the infected fraction grows at time $\tau = 0$ if and only if $R_0 (1 - \epsilon) > 1$.

## Depends on

- [Hawkes process with a time-varying reproduction number](hawkes-process-with-a-time-varying-reproduction-number.md)
- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

The prefactor $1 - I_c/N$ plays the role of the susceptible fraction $S/N$: each would-be infection lands on a susceptible host with that probability, which makes HawkesN a stochastic version of the SIR model; for large $R$ its trajectories are essentially deterministic. The rescaling is a direct substitution, $d/dt = \gamma\, d/d\tau$. Forecasts hold $R$ at its last estimate; fits to mortality need an assumed infection fatality ratio (1% as baseline) to convert deaths into infections. SIR, SEIR and HawkesN were fitted by Poisson maximum likelihood and compared by AIC on state-level data. Relaxing distancing without pharmaceutical interventions lets the epidemic re-emerge with little change in the final total.

## Sources

- A. L. Bertozzi, E. Franco, G. Mohler, M. B. Short, D. Sledge, "The challenges of modeling and forecasting the spread of COVID-19", Proceedings of the National Academy of Sciences of the USA (2020), Results, sections B and C ("Compartmental Models"), Eqs. (5)–(7), <https://doi.org/10.1073/pnas.2006520117> (PMC7382213).
