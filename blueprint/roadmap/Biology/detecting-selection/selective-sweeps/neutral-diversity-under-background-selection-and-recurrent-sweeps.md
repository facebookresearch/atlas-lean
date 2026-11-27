# Neutral diversity under background selection and recurrent sweeps

Consider an autosomal neutral site at position $x$ with local mutation rate $u(x)$ per generation, in a population whose effective size without linked selection is $N_e$. Let $B(x) \in (0,1]$ be the multiplicative reduction of the effective size caused by background selection at linked sites, and let $S(x)$ be the per-generation rate of coalescence forced by [recurrent selective sweeps](coalescence-rate-from-recurrent-selective-sweeps.md). The expected pairwise diversity at $x$ is approximately

$$\pi(x) = \frac{2u(x)}{2u(x) + \dfrac{1}{2N_eB(x)} + S(x)} .$$

With purifying selection at annotated sites $a_B(i_B)$, deleterious mutation rate $u_d(i_B)$ and a density $f(t \mid i_B)$ of heterozygous selection coefficients $t$, the background-selection factor is the [background selection reduction with recombination and a distribution of selection strengths](../../population-genetics/mutation-selection-balance/background-selection-with-recombination-and-a-distribution-of-effects.md), summed over the selected sites $y$:

$$B(x) = \exp\!\left(-\sum_{i_B}\sum_{y\in a_B(i_B)} \int \frac{u_d(i_B)\, t}{\bigl(t + r(x,y)(1-t)\bigr)^2}\, f(t\mid i_B)\, dt\right),$$

where $r(x,y)$ is the recombination distance. This approximation is valid when selection at each site is strong, $2N_et \gg 1$.

## Proof sketch

Trace two lineages back in time. Three competing exponential clocks act on them: a mutation on either lineage at total rate $2u$, coalescence by drift at rate $1/(2N_eB)$ in a population whose effective size has been reduced by background selection, and coalescence forced by a sweep at rate $S$. The probability that mutation comes first is the displayed ratio, and with $2u \ll$ the coalescence rates this is the expected heterozygosity. The factor $B$ multiplies site-by-site reductions, each given by the classical deleterious-site formula $u_d t/(t + r(1-t))^2$ integrated over the distribution of $t$. Writing the per-site term as $u_d/\bigl(t(1+r(1-t)/t)^2\bigr)$ shows that tightly linked strong selection contributes about $u_d/t$. Fitting this model by composite likelihood to polymorphism and divergence data gives a genome-wide map of $\pi(x)/\pi_0$.

## Depends on

- [Background selection reduces the effective size to the mutation-free class](../../population-genetics/mutation-selection-balance/background-selection-deterministic-reduction-fac.md)
- [Coalescence rate from recurrent selective sweeps](coalescence-rate-from-recurrent-selective-sweeps.md)
- [Background selection with recombination and a distribution of selection strengths](../../population-genetics/mutation-selection-balance/background-selection-with-recombination-and-a-distribution-of-effects.md)

## Sources

- E. Elyashiv, S. Sattath, T. T. Hu, A. Strutsovsky, G. McVicker, P. Andolfatto, G. Coop, G. Sella, *A genomic map of the effects of linked selection in Drosophila*, PLoS Genetics 12 (2016), e1006130, <https://doi.org/10.1371/journal.pgen.1006130>, PMCID PMC4990265. Diversity model Eq. (1); background selection Eq. (2); composite-likelihood fit in Methods.
- B. Charlesworth, M. T. Morgan, D. Charlesworth, *The effect of deleterious mutations on neutral molecular variation*, Genetics 134 (1993), 1289–1303, <https://doi.org/10.1093/genetics/134.4.1289>.
