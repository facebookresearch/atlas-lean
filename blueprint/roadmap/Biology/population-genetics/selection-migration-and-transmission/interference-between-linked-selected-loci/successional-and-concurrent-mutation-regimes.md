# Successional and concurrent regimes of beneficial mutations in an asexual population

Consider a purely asexual population of constant size $N$ in which beneficial mutations arise at total
rate $U_b$ per individual per generation, each raising fitness, defined as the exponential growth rate,
by the same amount $s > 0$. Fitness is additive, so an individual carrying $k$ such mutations has fitness
$(k-\ell)s$ above one carrying $\ell$ of them; there is no epistasis and no frequency-dependent
selection. Drift is modeled by a continuous-time branching process: every individual dies at rate $1$, an
individual carrying $y$ mutations gives birth at rate $1 + (y - \bar{y})s$, where $\bar{y}$ is the
population mean, and mutant offspring are produced at rate $U_b$ per individual. Under these dynamics a
new beneficial mutation survives drift with probability $\approx cs$ with $c = 1$, against $c = 2$ for the
Wright-Fisher model. Write $v = d\langle r\rangle/dt$ for the speed of evolution, the rate of increase of
mean fitness.

A single established mutant lineage grows at rate $s$ and so fixes in time of order $\ln[Ns]/s$, while
the waiting time for the next mutation destined to establish is of order $1/(NU_b s)$. Fixation precedes
establishment when

$$\tau_{\mathrm{fix}} \approx \frac{\ln[Ns]}{s} \ll \tau_{\mathrm{establish}} \approx \frac{1}{NU_b s},$$

which is the **successional-mutations regime**. There each mutation fixes before the next establishes,
substitutions occur at rate $NU_b s$, and

$$v = NU_b s^2 .$$

The opposite inequality,

$$NU_b \gtrsim \frac{1}{\ln[Ns]},$$

is the **concurrent-mutations regime**, in which establishment times are shorter than fixation times,
many mutant lineages segregate at once, and beneficial mutations arising in different lineages interfere.
Throughout, strong selection is assumed: $Ns \gg 1$, so drift matters only while a subpopulation is
rare, and $s/U_b \gg 1$.

In the concurrent regime define the **lead** $Q = qs$ of the fitness distribution as the difference
between the fitness of the most-fit individual and the mean fitness, so that the fittest individuals
carry $q$ more beneficial mutations than the average one; more precisely $Q - s$ is the gap between the
mean fitness and the fitness of the most-fit established class.

## Depends on

- [Clonal interference](clonal-interference.md)
- [Hill-Robertson interference](hill-robertson-interference.md)

## Expansion

The two regimes are separated by comparing the two timescales of a single sweep: the waiting time until a
mutation destined to survive drift appears, which scales as $1/(NU_b s)$, and the time for an established
lineage of advantage $s$ to grow from frequency $1/(Ns)$ to a large fraction of the population, which
scales as $\ln[Ns]/s$. When the first dominates, sweeps do not overlap and the substitution process is
mutation limited, which gives the linear dependence of $v$ on $NU_b$. When the second dominates, several
lineages are climbing at once, mutations occurring in unfit backgrounds are wasted, and the linear law
fails, so a different analysis, organized around the lead rather than the variance, is needed.

## Sources

- M. M. Desai and D. S. Fisher, "Beneficial mutation-selection balance and the effect of linkage on positive selection", Genetics 176 (2007), 1759-1798, <https://doi.org/10.1534/genetics.106.067678> (PMC1931526). (Equations 1-3, the "Simplest model" section.)
