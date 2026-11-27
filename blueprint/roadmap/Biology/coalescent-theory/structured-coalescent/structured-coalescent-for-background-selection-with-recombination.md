# Structured coalescent for background selection with recombination

Consider a haploid Wright–Fisher population of size $N$ at mutation–selection equilibrium and a genomic region of $L$ selected sites split into $K$ types, $L_k$ sites of type $k$. Deleterious mutations arise without back mutation at total rate $U_k$ per chromosome per generation on type-$k$ sites, have effect $s_k \in (0,1)$, and combine multiplicatively; crossing over in the region occurs with probability $R$ per generation, uniformly along it. Write $d = (d_1, \dots, d_K)$ for the numbers of deleterious mutations of each type carried by a chromosome, $\lambda_k = U_k/s_k$, $\gamma_k = N s_k$, $\rho = NR$, and measure time in units of $N$ generations.

**Model.** At equilibrium the counts are independent Poisson,

$$f(d) = \prod_{k=1}^{K} e^{-\lambda_k}\frac{\lambda_k^{d_k}}{d_k!},$$

and the sampled chromosomes start with independent $\mathrm{Poisson}(\lambda_k)$ counts. Backwards in time three competing exponential events act on the lineages:

- *mutation:* a lineage with counts $d$ loses one type-$k$ mutation (its parent had one fewer) at rate $d_k\gamma_k$, total rate $\sigma_m = \sum_{\text{lineages}}\sum_k d_k\gamma_k$;
- *recombination:* each lineage splits at rate $\rho$ at a uniform breakpoint; if $b_k$ type-$k$ sites lie left of it, the left parent inherits a $\mathrm{Binomial}(d_k, b_k/L_k)$ number of the lineage's type-$k$ mutations and the right parent the rest, while the non-ancestral segments of the two parents carry $\mathrm{Poisson}((1 - b_k/L_k)\lambda_k)$ and $\mathrm{Poisson}((b_k/L_k)\lambda_k)$ mutations;
- *coalescence:* each lineage carries a genetic background $G = (G_1, \dots, G_K)$, where $G_k$ cuts the type-$k$ sites into consecutive intervals (at the breakpoints of the recombination events in its ancestry) and records the number of type-$k$ mutations in each interval. Two lineages $i$ and $j$ can coalesce only if, for every $k$, $G^{(i)}_k$ and $G^{(j)}_k$ are compatible, that is, both could have been inherited from one parent (in particular they carry the same numbers $d = (d_1, \dots, d_K)$ of mutations; Zeng and Charlesworth 2011, Figure 3). The two backgrounds then determine the background $G^{(a)}$ of their potential common ancestor, which also carries $d$ mutations, and the per-generation coalescence probability is (Equations (4) and (5))

$$p_c = \frac{1}{N}\,\frac{P(G^{(a)})}{f(d)\,P(G^{(i)})\,P(G^{(j)})}, \qquad P(G) = \prod_{k=1}^{K} P(G_k).$$

  Here, if $G_k$ has intervals holding fractions $\ell_1, \dots, \ell_B$ of the type-$k$ sites and counts $y_1, \dots, y_B$ with $\sum_b y_b = d_k$, then $P(G_k) = \dfrac{d_k!}{\prod_b y_b!}\prod_b \ell_b^{\,y_b}$ is the multinomial proportion, among chromosomes carrying $d_k$ type-$k$ mutations, of those whose mutations are placed as $G_k$ specifies (Equation (10) of Zeng and Charlesworth 2011). Writing $F(G) = f(d)P(G)$ for the population frequency of background $G$, the pair coalesces at rate $Np_c = F(G^{(a)})/\big(F(G^{(i)})F(G^{(j)})\big)$ on the $N$ time scale.

**Changing population size.** For strongly selected mutations the per-generation probabilities of losing a mutation ($\approx \sum_k d_k s_k$) and of recombination ($R$) do not depend on population size, so with time scaled by $N(0)$, $\gamma_k = N(0)s_k$ and $\rho = N(0)R$ stay fixed, and only the coalescence probability is recomputed with $N(t)$ in place of $N$.

**Special case (one type, no recombination).** Backgrounds are then just counts $d$, and two lineages in class $d$ coalesce at rate $1/f(d)$ while each moves to class $d - 1$ at rate $d\gamma$. When $\gamma \to \infty$ lineages reach the mutation-free class almost immediately and coalesce there at rate $1/f(0) = e^{\lambda}$, which recovers the classical reduction $N_e/N = e^{-U/s}$ of neutral diversity.

## Remarks

The deleterious-mutation classes play the role of demes: a lineage "migrates" from class $d$ to class $d - 1$ backwards in time when its ancestor did not yet carry one of its mutations, and coalescence is confined to a class whose size is $Nf(d)$, so the pairwise rate in a class of size $Nf(d)$ is $1/f(d)$ on the $N$ time scale. Recombination makes backgrounds piecewise, so the model records, for every lineage, how many mutations of each type sit in each ancestral interval; compatibility of two backgrounds and the frequencies of their joint ancestral background and of the two descendant backgrounds determine $p_c$. Neutral sites can be interleaved freely; they change only how breakpoints split the selected backgrounds, and variability at selected and neutral sites can be generated jointly along the reconstructed genealogy. Zeng checks the model against forward simulations, including variable selection coefficients and recent population growth.

## Depends on

- [Poisson equilibrium of multiplicative mutation–selection balance](../../population-genetics/mutation-selection-balance/multilocus-multiplicative-mutation-selection-poi.md)
- [Background selection reduces the effective size to the mutation-free class](../../population-genetics/mutation-selection-balance/background-selection-deterministic-reduction-fac.md)

## Sources

- K. Zeng, "A coalescent model of background selection with recombination, demography and variation in selection coefficients", Heredity 110 (2013), 363–371, section "Theory" (Equations (1)–(5) and subsections "Neutral sites" and "Changes in population size"), <https://doi.org/10.1038/hdy.2012.102> (PMCID: PMC3607694).
- K. Zeng and B. Charlesworth, "The joint effects of background selection and genetic recombination on local gene genealogies", Genetics 189 (2011), 251–266, Equations (7), (8) and (10) and Figure 3, <https://doi.org/10.1534/genetics.111.130575> (PMCID: PMC3176134).
