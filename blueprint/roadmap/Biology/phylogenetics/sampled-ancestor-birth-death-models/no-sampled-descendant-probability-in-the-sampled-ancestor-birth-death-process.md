# No-sampled-descendant probability in the sampled-ancestor birth–death process

**Model.** Time $t$ runs backwards from the present ($t = 0$). Starting from one lineage at the origin time $x_0$, each lineage independently speciates (transmits) at rate $\lambda > 0$, goes extinct (becomes uninfectious) at rate $\mu \ge 0$, and is sampled at rate $\psi \ge 0$; at each sampling event the lineage is removed with probability $r \in [0,1]$ and otherwise continues. At the present each surviving lineage is sampled with probability $\rho \in [0,1]$. With $r < 1$, sampled lineages can have sampled descendants and appear as degree-two nodes (**sampled ancestors**) of the reconstructed tree. The case $r = 0$, $\rho > 0$ is the **fossilized birth–death process**; the case $\rho = 0$ is the transmission birth–death process.

**Proposition.** Let $p_0(t)$ be the probability that a lineage alive at time $t$ before the present has no sampled descendants. Then $p_0$ solves the Riccati equation

$$p_0'(t) = \mu - (\lambda + \mu + \psi)\, p_0(t) + \lambda\, p_0(t)^2, \qquad p_0(0) = 1 - \rho,$$

whose solution is

$$p_0(t) = \frac{1}{2\lambda}\left[\lambda + \mu + \psi + c_1\, \frac{e^{-c_1 t}(1 - c_2) - (1 + c_2)}{e^{-c_1 t}(1 - c_2) + (1 + c_2)}\right],$$

$$c_1 = \sqrt{(\lambda - \mu - \psi)^2 + 4\lambda\psi}, \qquad c_2 = -\frac{\lambda - \mu - 2\lambda\rho - \psi}{c_1}.$$

As $t \to \infty$, $p_0(t)$ converges to the smaller root $(\lambda + \mu + \psi - c_1)/(2\lambda)$ of $\lambda x^2 - (\lambda + \mu + \psi)x + \mu = 0$.

**Corollary (sampled-ancestor probability).** An individual sampled at time $t$ before the present appears as a sampled ancestor in the reconstructed tree with probability

$$(1 - r)\,\big(1 - p_0(t)\big).$$

## Expansion

Condition on the first event in a short interval $[t, t + dt]$ looking forward in time from $t$: with probability $\mu\,dt$ the lineage dies (no sampled descendants), with probability $\lambda\,dt$ it splits and both daughters must leave no sample ($p_0^2$), and with probability $\psi\,dt$ it is sampled, which is incompatible with having no sampled descendants (the sample itself is observed). Collecting terms gives the Riccati equation, and its constant-coefficient solution follows from the roots $x_\pm = (\lambda + \mu + \psi \pm c_1)/(2\lambda)$, using $(\lambda + \mu + \psi)^2 - 4\lambda\mu = (\lambda - \mu - \psi)^2 + 4\lambda\psi$; at $t = 0$ the bracket equals $\lambda + \mu + \psi - c_1 c_2 = 2\lambda(1 - \rho)$. A sampled individual is a sampled ancestor exactly when it stays in the process (probability $1 - r$) and then leaves at least one sampled descendant (probability $1 - p_0(t)$). The function $p_0$ is the main ingredient of the reconstructed-tree densities of these models; for the transmission process with $\rho = 0$ the tree density depends on $(\lambda, \mu, \psi, r)$ only through three combinations, so one parameter must be fixed for inference, whereas under the fossilized birth–death process all four of $(\lambda, \mu, \psi, \rho)$ are estimable.

## Sources

- Gavryushkina A, Welch D, Stadler T, Drummond AJ, "Bayesian inference of sampled ancestor trees for epidemiology and fossil calibration" (2014), Methods, "The sampled ancestor birth-death model" (definition of $p_0$, the sampled-ancestor probability and the identifiability statement), <https://doi.org/10.1371/journal.pcbi.1003919>, PMCID PMC4263412.
- T. Stadler, "Sampling-through-time in birth-death trees", Journal of Theoretical Biology 267 (2010) 396–404, <https://doi.org/10.1016/j.jtbi.2010.09.010>.
