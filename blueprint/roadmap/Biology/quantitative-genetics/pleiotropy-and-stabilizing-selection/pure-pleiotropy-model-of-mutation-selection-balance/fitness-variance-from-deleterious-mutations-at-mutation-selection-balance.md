# Variance in fitness from deleterious mutations at mutation–selection balance

Consider a diploid population at a site where a deleterious, semidominant allele arises by mutation at rate $u$ per generation, with genotype fitnesses $1$, $1 - s$ and $1 - 2s$ for $0 < u \ll s \le 1/2$. Ignoring drift, the allele is held near the equilibrium frequency $q^* \approx u/s$ (the [diploid mutation–selection equilibrium](../../../population-genetics/mutation-selection-balance/diploid-step-mult-fixed.md)). A segregating allele at frequency $x$ contributes additive variance $2x(1-x)s^2$ in fitness, so at equilibrium the site contributes

$$V \approx 2 q^* s^2 \approx 2us.$$

Summing over independent sites $i$ with mutation rates $u_i$ and selection coefficients $s_i$, the additive variance in fitness is $\sum_i 2u_i s_i = 2U\bar s$, where $U = \sum_i u_i$ is the total mutation rate of the class and $\bar s = \sum_i u_i s_i / U$ is its mutation-weighted mean selection coefficient. A class of mutations therefore contributes variance in proportion to its total mutation rate times its mean strength of selection: strongly selected mutations, though rare, contribute more variance per mutation than weakly selected ones.

## Proof sketch

With additive (semidominant) effects, the average effect of the allele on fitness is $-s$, so the additive variance at frequency $x$ is $2x(1-x)s^2$. Because $q^* \ll 1$, $2q^*(1-q^*)s^2 \approx 2q^* s^2$, and substituting $q^* \approx u/s$ gives $2us$. With drift the frequency fluctuates, but for $4N_e s \gg 1$ the mean frequency is still approximately $u/s$ and the variance is approximately linear in the frequency, so the same expression holds on average. Additivity across freely recombining sites gives the sum.

## Depends on

- [The frequency $U/s$ is an equilibrium](../../../population-genetics/mutation-selection-balance/diploid-step-mult-fixed.md)

## Sources

- A. Eyre-Walker, Genetic architecture of a complex trait and its implications for fitness and genome-wide association studies, *Proc. Natl. Acad. Sci. USA* 107 (2010), 1752–1756, <https://doi.org/10.1073/pnas.0906182107>, PMCID PMC2868283 (Results, the argument following Fig. 2; Discussion on categories of mutations).
