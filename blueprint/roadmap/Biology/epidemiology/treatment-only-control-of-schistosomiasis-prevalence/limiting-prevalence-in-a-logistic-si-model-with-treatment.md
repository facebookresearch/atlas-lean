# Limiting prevalence in a logistic SI model with treatment

Let $p_0(t)$ and $p_1(t)$ be the numbers of uninfected and infected individuals in a population endemic for an infection such as *Schistosoma mansoni*, with constant infection rate $\beta > 0$, treatment (recovery) rate $\gamma \ge 0$, withdrawal (death or migration) rate $\mu > 0$, birth-rate parameter $\nu > 0$, and maximal population size $n$. Newborns are uninfected:

$$
\frac{dp_0}{dt} = -\beta p_0 - \mu p_0 + \gamma p_1 + \nu(n - p_0 - p_1)(p_0 + p_1), \qquad \frac{dp_1}{dt} = \beta p_0 - (\mu + \gamma) p_1 .
$$

The total population $P = p_0 + p_1$ follows the logistic law $P' = \nu\big(\tfrac{\nu n - \mu}{\nu} - P\big)P$, and $\Delta = \{0 \le p_0 + p_1 \le n\}$ is invariant.

**Theorem.** Suppose $\nu, \gamma, \beta, \mu, n > 0$ and $\nu n - \mu > 0$. For every initial state with $0 < p_0 + p_1 \le n$, whatever the initial number infected, the prevalence satisfies

$$
\frac{p_1(t)}{p_0(t) + p_1(t)} \longrightarrow \frac{\beta}{\gamma + \mu + \beta} \quad \text{as } t \to \infty .
$$

Consequently, treatment alone lowers the long-run prevalence to $\beta/(\beta + \mu + \gamma)$ but never eliminates the infection while transmission continues ($\beta > 0$).

## Depends on

- [Logistic growth equation](../../population-dynamics/logistic-growth-equation/logistic.md)

## Expansion

The prevalence $\pi = p_1/P$ satisfies the scalar equation

$$
\pi' = \beta(1 - \pi) - (\mu + \gamma)\pi - \frac{P'}{P}\pi .
$$

Since $P(t)$ converges to the carrying capacity $(\nu n - \mu)/\nu$, the term $P'/P$ tends to $0$. The equation becomes asymptotically autonomous with the globally attracting fixed point $\pi^* = \beta/(\beta + \mu + \gamma)$. The limit does not depend on the demographic parameters $\nu$ and $n$.

## Sources

- Roberta Oliveira-Prado, Máderson Alvares de Souza Cabral, Sylvie Oliffson Kamphorst, Sônia Pinto-de-Carvalho, "Modeling the prevalence of Schistosoma mansoni infection in an endemic population", arXiv (2017). Section 2, Theorem 1. <https://doi.org/10.48550/arXiv.1702.05083>
