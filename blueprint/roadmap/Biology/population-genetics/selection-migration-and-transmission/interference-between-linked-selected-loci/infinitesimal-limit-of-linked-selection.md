# Infinitesimal limit of linked selection

Consider $N$ haploid individuals carrying one non-recombining chromosome ($R = 0$). New selected mutations arise at total rate $U$ per genome per generation, each with fitness effect $s$ (more generally drawn from a fixed distribution of fitness effects $\rho(s)$, beneficial or deleterious, with no epistasis). Since all genotypes with the same fitness are equivalent, the population state is the fitness-class distribution $f(X)$, and a neutral marker site is followed by splitting $f(X)$ into the classes carrying the ancestral and the derived allele. Write $\pi_0$ for the neutral pairwise diversity and $\sigma^2$ for the variance in fitness within the population.

**Background selection limit.** Let $Ns \to \infty$ with $\lambda = U/s$ fixed. The fitness classes approach the independent-sites prediction, with the number $k$ of deleterious mutations in an individual distributed as $\mathrm{Poisson}(\lambda)$, and the neutral site behaves as in an unstructured neutral population of size $N e^{-\lambda}$:

$$\frac{\pi}{\pi_0} \to e^{-U/s},$$

with the shape of the site frequency spectrum unchanged.

**Infinitesimal limit.** Let instead $Ns \to 0$ and $NU \to \infty$ with the product

$$NU\,(Ns)^2 \qquad \bigl(\text{for a distribution of effects, } NU\,\langle (Ns)^2 \rangle\bigr)$$

held fixed. In a nearly neutral population the fitness variance is the mutational spread accumulated over the coalescent timescale $T_c \sim N$, of order $\sigma^2 \sim U s^2 T_c$, so $(N\sigma)^2$ stays finite exactly when $NU(Ns)^2$ does. In this limit the fitness distribution and every summary of neutral diversity (the reduction $\pi/\pi_0$ and the normalized site frequency spectrum) depend on the parameters only through $NU\langle (Ns)^2\rangle$, equivalently through $N\sigma$, which is a monotone function of it. Individual selected mutations are effectively neutral, yet the genealogy is strongly distorted: an excess of rare alleles, and a non-monotone ("U-shaped") high-frequency tail that no exchangeable coalescent without multiple mergers can produce. The two ends are known: $N\sigma \to 0$ recovers the neutral coalescent, and $N\sigma \gg 1$ approaches the Bolthausen–Sznitman coalescent, whose normalized site frequency spectrum is parameter-free while $\pi/\pi_0$ decays as a power of $N\sigma$.

Consequently, in the interference selection regime two asexual populations with the same $N\sigma$ show nearly identical patterns of neutral variation, whatever the fitness effects of the selected mutations; neutral diversity cannot separate $U$ from $s$ there.

## Depends on

- [Background selection reduces the effective size to the mutation-free class](../../mutation-selection-balance/background-selection-deterministic-reduction-fac.md)
- [Clonal interference](clonal-interference.md)

## Expansion

The fitness classes follow the Langevin dynamics of the multi-locus diffusion: deterministic selection $(X - \bar X) f$, mutation moving mass from class $X$ to $X - s$ at rate $U$, and a genetic-drift noise term of variance $f/N$. Rescaling the moment generating function of these dynamics shows that when $Ns \to 0$ only the second moment of the mutational kernel survives, through $NU\langle(Ns)^2\rangle$; this is the linked analogue of the infinitesimal model of quantitative genetics, with fitness as the trait. Beneficial and deleterious effects enter symmetrically. Traveling-wave theory gives $N\sigma$ as an increasing function of $NU(Ns)^2$; because of interference, $\sigma^2$ lies far below the independent-sites value $Us$ and grows sublinearly in the number of selected loci. Simulations over $10 \le NU \le 10^4$ and $10^{-3} \le Ns \le 10^3$ show the collapse: $\pi/\pi_0$ is predicted by $\lambda$ in the background selection regime and by $N\sigma$ in the interference regime, and frequency-spectrum distortions (Tajima's $D$, mean minor allele frequency, the U-shape statistic) track $\pi/\pi_0$ in the latter.

## Sources

- B. H. Good, A. M. Walczak, R. A. Neher and M. M. Desai, "Genetic diversity in the interference selection limit", PLoS Genetics (2014), e1004222, Results sections "The model", "Background: Existing predictions break down in the interference selection regime", "Patterns of diversity collapse onto a single parameter family" and "The infinitesimal limit" (Eqs. (1), (2), (4) and (5); Text S2), <https://doi.org/10.1371/journal.pgen.1004222>, PMCID PMC3967937.
