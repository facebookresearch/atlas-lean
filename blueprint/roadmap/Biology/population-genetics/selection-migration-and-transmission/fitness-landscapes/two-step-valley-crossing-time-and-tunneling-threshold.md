# Two-step valley-crossing time and the tunneling threshold

In the [mutant-lineage model of a fitness valley](success-probability-of-a-mutant-lineage-in-a-fitness-valley.md) with $K = 2$, a haploid population of size $N$ starts at the wild type (fitness $1$). Single mutants arise at rate $\mu_0$ per individual and have fitness $1-\delta_1$; they mutate at rate $\mu_1$ to the double mutant, which has fitness $1+s$ with $1/N \ll s \ll 1$.

**Stochastic tunneling.** A single mutant gives rise to an established double mutant without first fixing with probability

$$p_1 = \frac{-\delta_1 + \sqrt{\delta_1^2 + 4\mu_1 s}}{2} \approx \begin{cases} \sqrt{\mu_1 s}, & \delta_1 \ll 2\sqrt{\mu_1 s},\\ \mu_1 s/\delta_1, & \delta_1 \gg 2\sqrt{\mu_1 s}. \end{cases}$$

If $N\mu_0 \ll 1$ and tunneling dominates, the expected time until the double mutant establishes is

$$\tau \approx \frac{1}{N\mu_0 p_1} \approx \begin{cases} 1/(N\mu_0\sqrt{\mu_1 s}), & \text{effectively neutral intermediates},\\ \delta_1/(N\mu_0\mu_1 s), & \text{strongly deleterious intermediates}. \end{cases}$$

**Threshold population size.** A single mutant fixes by drift with probability

$$\rho_1 = \frac{e^{\delta_1} - 1}{e^{N\delta_1} - 1}.$$

Tunneling dominates when $p_1 \gg \rho_1$ and sequential fixation when $\rho_1 \gg p_1$; the two are equal at

$$N_\times = \frac{1}{\delta_1}\log\!\left(1 + \frac{e^{\delta_1}-1}{p_1}\right),$$

which is approximately $1/\sqrt{\mu_1 s}$ for effectively neutral intermediates. For $N < N_\times$ the expected crossing time by sequential fixation is approximately

$$\tau_{\mathrm{seq}} \approx \frac{1}{N\mu_0\rho_1} + \frac{1}{N\mu_1(s+\delta_1)}.$$

## Proof sketch

With $p_2 = s$ the recursion for $p_1$ is the $K=2$ case of the general formula. Successful single mutants arise as a Poisson process of rate $N\mu_0 p_1$, so the waiting time for the first is exponential with mean $1/(N\mu_0 p_1)$; when $N\mu_0 \ll 1$ this dominates the drift time of the successful lineage and the establishment time of the double mutant. The fixation probability $\rho_1$ is Kimura's haploid formula for selection coefficient $-\delta_1$. Comparing $p_1$ with $\rho_1$ locates the crossover: a neutral single mutant fixes with probability $1/N$, which exceeds $\sqrt{\mu_1 s}$ exactly when $N < 1/\sqrt{\mu_1 s}$. Below $N_\times$, the crossing time is the time to produce a single mutant destined to fix plus the time for that fixed background to produce an established double mutant, whose establishment probability is about $s + \delta_1$ relative to the fixed single-mutant background. The strongly deleterious case recovers the result of Weinreich and Chao for a haploid population when $\mu_0 = \mu_1$.

## Depends on

- [Success probability of a mutant lineage in a fitness valley](success-probability-of-a-mutant-lineage-in-a-fitness-valley.md)
- [Kimura's fixation probability](../../diffusion-theory/wright-fisher-diffusion/kimura-fixation.md)

## Sources

- D. B. Weissman, M. M. Desai, D. S. Fisher, M. W. Feldman, *The rate at which asexual populations cross fitness valleys*, Theoretical Population Biology 75 (2009), 286–300, <https://doi.org/10.1016/j.tpb.2009.02.006>, PMCID PMC2992471. Section IV.C, Eqs. (25)–(28); Section IV.D, Eqs. (29)–(32).
