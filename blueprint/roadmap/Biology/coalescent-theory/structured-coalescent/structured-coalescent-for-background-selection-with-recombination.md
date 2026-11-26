# Structured coalescent for background selection with recombination

Consider a haploid Wright–Fisher population of size $N$ at mutation–selection equilibrium and a genomic region of $L$ selected sites split into $K$ types, $L_k$ sites of type $k$. Deleterious mutations arise without back mutation at total rate $U_k$ per chromosome per generation on type-$k$ sites, have effect $s_k \in (0,1)$, and combine multiplicatively; crossing over in the region occurs with probability $R$ per generation, uniformly along it. Write $d = (d_1, \dots, d_K)$ for the numbers of deleterious mutations of each type carried by a chromosome, $\lambda_k = U_k/s_k$, $\gamma_k = N s_k$, $\rho = NR$, and measure time in units of $N$ generations.

**Model.** At equilibrium the counts are independent Poisson,
$$f(d) = \prod_{k=1}^{K} e^{-\lambda_k}\frac{\lambda_k^{d_k}}{d_k!},$$
and the sampled chromosomes start with independent $\mathrm{Poisson}(\lambda_k)$ counts. Backwards in time three competing exponential events act on the lineages:

- *mutation:* a lineage with counts $d$ loses one type-$k$ mutation (its parent had one fewer) at rate $d_k\gamma_k$, total rate $\sigma_m = \sum_{\text{lineages}}\sum_k d_k\gamma_k$;
- *recombination:* each lineage splits at rate $\rho$ at a uniform breakpoint; if $b_k$ type-$k$ sites lie left of it, the left parent inherits a $\mathrm{Binomial}(d_k, b_k/L_k)$ number of the lineage's type-$k$ mutations and the right parent the rest, while the non-ancestral segments of the two parents carry $\mathrm{Poisson}((1 - b_k/L_k)\lambda_k)$ and $\mathrm{Poisson}((b_k/L_k)\lambda_k)$ mutations;
- *coalescence:* two lineages can coalesce only if their recorded genetic backgrounds (mutation counts on each tracked interval) are compatible, at a rate $Np_c$ inversely proportional to the frequency of their common ancestral background in the population.

**Changing population size.** For strongly selected mutations the per-generation probabilities of losing a mutation ($\approx \sum_k d_k s_k$) and of recombination ($R$) do not depend on population size, so with time scaled by $N(0)$, $\gamma_k = N(0)s_k$ and $\rho = N(0)R$ stay fixed, and only the coalescence probability is recomputed with $N(t)$ in place of $N$.

**Special case (one type, no recombination).** Backgrounds are then just counts $d$, and two lineages in class $d$ coalesce at rate $1/f(d)$ while each moves to class $d - 1$ at rate $d\gamma$. When $\gamma \to \infty$ lineages reach the mutation-free class almost immediately and coalesce there at rate $1/f(0) = e^{\lambda}$, which recovers the classical reduction $N_e/N = e^{-U/s}$ of neutral diversity.

## Depends on

- [Poisson equilibrium of multiplicative mutation–selection balance](../../population-genetics/mutation-selection-balance/multilocus-multiplicative-mutation-selection-poi.md)
- [Background selection reduces the effective size to the mutation-free class](../../population-genetics/mutation-selection-balance/background-selection-deterministic-reduction-fac.md)
- [Structured coalescent for n lineages with a general migration matrix](structured-coalescent-for-n-lineages-with-a-gene.md)

## Expansion

The deleterious-mutation classes play the role of demes: a lineage "migrates" from class $d$ to class $d - 1$ backwards in time when its ancestor did not yet carry one of its mutations, and coalescence is confined to a class whose size is $Nf(d)$, so the pairwise rate in a class of size $Nf(d)$ is $1/f(d)$ on the $N$ time scale. Recombination makes backgrounds piecewise, so the model records, for every lineage, how many mutations of each type sit in each ancestral interval; compatibility of two backgrounds and the frequency of their joint ancestor determine $p_c$. Neutral sites can be interleaved freely; they change only how breakpoints split the selected backgrounds, and variability at selected and neutral sites can be generated jointly along the reconstructed genealogy. Zeng checks the model against forward simulations, including variable selection coefficients and recent population growth.

## Sources

- K. Zeng, "A coalescent model of background selection with recombination, demography and variation in selection coefficients", Heredity 110 (2013), 363–371, section "Theory" (Equations (1)–(5) and subsections "Neutral sites" and "Changes in population size"), <https://doi.org/10.1038/hdy.2012.102> (PMCID: PMC3607694).
