# Household-based and acquaintance vaccination on household-structured networks

**Setting.** The SIR model on households embedded in a configuration network, with notation as in the threshold article ($\tilde\rho_n$, $\tilde C^{(n)}$ the global offspring of a single-household epidemic in a household of size $n$ started by a globally infected case, $R_*$ the pre-vaccination threshold).

**Household-based allocation.** Let $x_{nv}$ be the fraction of size-$n$ households with $v$ vaccinated members. The coverage is

$$p_V = \sum_{n}\tilde\rho_n\sum_{v=0}^n \frac{v}{n}\,x_{nv}.$$

Under an all-or-nothing vaccine (each vaccinee fully immune with probability $\varepsilon$, otherwise unaffected) the post-vaccination threshold is

$$R_v = \sum_n \tilde\rho_n \sum_{v=0}^n x_{nv}\,\mu_{n,v}, \qquad \mu_{n,v} = \sum_{k=0}^{v}\binom{v}{k}\varepsilon^k(1-\varepsilon)^{v-k}\,\frac{n-k}{n}\,E\big[\tilde C^{(n-k)}\big],$$

and a major outbreak is possible iff $R_v > 1$. For a non-random vaccine response (relative susceptibility $a$, infectivity $b$) $R_v$ is the dominant eigenvalue of a $2\times 2$ mean offspring matrix; it takes the same linear form when that matrix has rank one, which holds for a leaky vaccine ($b = 1$) or $a = 1$.

**Optimal allocation.** With a maximum household size, both "minimize $p_V$ subject to $R_v \le 1$" and "minimize $R_v$ subject to a coverage bound" are linear programs in the household counts. Writing $R_v = \sum_{(n,v)} h_{nv} M_{n,v}$ over households and $G_{n,v} = M_{n,v} - M_{n,v+1}$ for the reduction from one more vaccination in a household in state $(n,v)$: if $G_{n,v}$ is decreasing in $v$ for each $n$, an optimal scheme vaccinates individuals greedily in order of decreasing $G_{n,v}$ until the target is met; otherwise only states on the lower convex hull of $\{(v, G_{n,v})\}$ can occur in an optimum.

**Acquaintance vaccination.** Each individual is sampled independently with probability $p_S$ and each sampled individual nominates each global neighbour independently with probability $p_N$; nominees are vaccinated. The coverage is

$$p_V = 1 - f_D(1 - p_S p_N),$$

and the early epidemic is a 6-type household branching process (primary case named by its infector, otherwise vaccinated, or unvaccinated; sampled or not), which keeps neighbour degrees independent and avoids typing by degree.

## Depends on

- [Threshold and final size for SIR epidemics on households embedded in a configuration network](threshold-and-final-size-for-households-on-configuration-networks.md)

## Expansion

$\mu_{n,v}$ averages over the number $k$ of successful vaccinations: the globally contacted member is susceptible with probability $(n-k)/n$, and then triggers a household epidemic among the $n-k$ susceptibles. Because $R_v$ and $p_V$ are both linear in the allocation, the optimization is a fractional knapsack whose greedy solution is optimal under diminishing returns, as for the households-only model. Acquaintance vaccination exploits the friendship paradox: a nominated individual has size-biased degree $\tilde D$, so with heavy-tailed $D$ it reduces $R_v$ far more per dose than any household-based scheme. When coverage cannot reach $R_v \le 1$ and the vaccine is imperfect, the scheme minimizing $R_v$ need not minimize the outbreak probability or the final size.

## Sources

- F. Ball, D. Sirl, "Evaluation of vaccination strategies for SIR epidemics on random networks incorporating household structure", Journal of Mathematical Biology 76 (2018) 483–530, Sect. 3 with equations (3.1)–(3.5), (3.12)–(3.13), and Sect. 4 with equation (4.1), <https://doi.org/10.1007/s00285-017-1139-0>, PMCID: PMC5754546.
