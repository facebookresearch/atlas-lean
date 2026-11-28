# Probability of k-step evolutionary rescue

Consider an asexual population of $N_0$ wild-type individuals with growth rate $m_0 < 0$ (so it declines to extinction without adaptation). Each individual produces mutants at rate $U$ per generation, and a mutant of a genotype with growth rate $m$ has growth rate $m'$ with density $f(m' \mid m)$ (in Fisher's geometric model, a scaled noncentral $\chi^2_n$ density with maximal growth rate $m_{\max}$ and mutational variance $\lambda$, Eq. 1). Demography is approximated by a diffusion.

**Rescue from the founders** (Eq. 2). If $p_0$ is the probability that one wild-type individual has descendants that rescue the population, then

$$P(\text{rescue}) = 1 - (1 - p_0)^{N_0} \approx 1 - e^{-N_0 p_0}.$$

**Lineage doomed alone** (Eq. 3). A single copy of a genotype with growth rate $m$, fated for extinction but producing rescue genotypes at rate $\Lambda(m)$, rescues the population with probability

$$p\big(m, \Lambda(m)\big) = 1 - \exp\!\Big[ |m| \Big( 1 - \sqrt{1 + 2\Lambda(m)/m^2} \Big) \Big].$$

Then $p_0 = p\big(m_0, \sum_{i \ge 1} \Lambda_i(m_0)\big)$, where $\Lambda_i$ is the rate of producing rescue genotypes carrying $i$ new mutations.

**Establishment** (Eq. 4). A lineage with growth rate $m$, ignoring further mutation, establishes with probability $p_{\mathrm{est}}(m) \approx 1 - e^{-2m}$ for $m > 0$ and $0$ for $m \le 0$.

**Recursion** (Eqs. 5–7). One-step rescue occurs at rate

$$\Lambda_1(m_0) = U \int_0^{m_{\max}} f(m \mid m_0)\, p_{\mathrm{est}}(m)\, dm,$$

and for $k \ge 2$, rescue through a first-step mutant that does not establish on its own but whose lineage produces $(k-1)$-step rescue occurs at rate

$$\Lambda_k(m_0) = U \int_{-\infty}^{m_{\max}} f(m \mid m_0)\, \big[1 - p_{\mathrm{est}}(m)\big]\, p\big(m, \Lambda_{k-1}(m)\big)\, dm.$$

## Depends on

- [Probability that a random mutation is beneficial](../beneficial-prob.md)

## Expansion

The founders act independently, giving Eq. 2. Eq. 3 is the probability that a subcritical branching diffusion, which spawns successful rescue lineages at rate $\Lambda$ per individual, produces at least one before dying out; for $2\Lambda \ll m^2$ it is $\approx \Lambda/|m|$, the expected number of rescue mutants produced during the doomed lineage's lifetime (total size $\approx 1/|m|$). The approximation $p_{\mathrm{est}} \approx 2m$ recovers Haldane's $2s$ at constant size. The recursion chains these: a $k$-step path is a non-establishing first mutant whose own lineage is rescued by $(k-1)$-step paths.

## Sources

- M. M. Osmond, S. P. Otto, G. Martin, *Genetic paths to evolutionary rescue and the distribution of fitness effects along them*, Genetics (2020). <https://doi.org/10.1534/genetics.119.302890> (PMCID: PMC7017017)
