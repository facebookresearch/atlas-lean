# Hawkes process with a time-varying reproduction number

Let $t_1 < t_2 < \dots$ be infection (or case) times. In the self-exciting branching point process the conditional intensity is

$$\lambda(t) = \mu + \sum_{t_i < t} R(t_i)\, w(t - t_i), \tag{1}$$

where $\mu \ge 0$ is the rate of exogenous cases, $R(t) \ge 0$ is the dynamic reproduction number, and $w$ is a probability density on $(0, \infty)$ (gamma or Weibull) for the time between an infection and the infections it causes. Equivalently, each event $j$ independently generates a Poisson number of direct offspring with mean $R(t_j)$, placed at times $t_j$ plus independent draws from $w$, and exogenous events form a Poisson process of rate $\mu$.

Given events $t_1, \dots, t_n$, the probability that event $i$ was caused by event $j < i$ is

$$p_{ij} = \frac{R(t_j)\, w(t_i - t_j)}{\lambda(t_i)}, \tag{2}$$

and $p_{ii} = \mu / \lambda(t_i)$ is the probability that $i$ is exogenous, so that $p_{ii} + \sum_{j < i} p_{ij} = 1$. With a histogram parameterization $R(t) = \sum_{k=1}^{B} r_k \mathbf{1}\{t \in I_k\}$ over time intervals $I_k$ (Eq. 3), the expectation–maximization update is

$$r_k = \frac{1}{N_k}\sum_{t_i > t_j} p_{ij}\, \mathbf{1}\{t_j \in I_k\}, \tag{4}$$

where $N_k$ is the number of events in $I_k$: the average expected number of offspring of the events in each interval.

Properties:

- since $\int_0^\infty w = 1$, an event at $t_j$ contributes $R(t_j)$ expected direct offspring, so $R$ is a reproduction number in the branching-process sense, and the process is subcritical near times where $R < 1$;
- early in an outbreak with constant $R$ and few depleted susceptibles, the process approximates the SIR model; incidence grows like $I(t) = I_0 e^{\alpha t}$, with doubling time $T_d = \ln 2 / \alpha$.

## Expansion

Equation (2) is Bayes' rule for the latent branching structure: event $i$ was caused by the background or by one earlier event, with probabilities proportional to their contributions to $\lambda(t_i)$. The expectation–maximization algorithm alternates between computing $p_{ij}$ and re-estimating $r_k$ by attributed offspring counts (and $\mu$ and the parameters of $w$ by analogous weighted averages). Fitted to mortality data from late January to early April 2020, the estimates of $R(t)$ dropped below $1$ in China by mid-February, decreased in Italy but stayed above $1$, and were around $2.5$ for the United States as a whole.

## Sources

- A. L. Bertozzi, E. Franco, G. Mohler, M. B. Short, D. Sledge, "The challenges of modeling and forecasting the spread of COVID-19", Proceedings of the National Academy of Sciences of the USA (2020), Results, sections A ("Exponential Growth") and B ("Self-Exciting Branching Process"), Eqs. (1)–(4), <https://doi.org/10.1073/pnas.2006520117> (PMC7382213).
