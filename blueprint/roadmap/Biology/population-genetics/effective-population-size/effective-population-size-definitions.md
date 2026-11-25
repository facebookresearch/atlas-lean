# Inbreeding, variance and eigenvalue effective population sizes

For a model of a diploid population at one biallelic neutral locus, three effective population sizes compare a
one-generation change with that of a Wright–Fisher population of $N_e$ diploids ($2N_e$ gene copies):

- the **inbreeding effective size** $N_e^{(i)}$ is defined by $1 - F_{t+1} = \bigl(1 - \frac{1}{2N_e^{(i)}}\bigr)(1 - F_t)$, where $F_t$ is the probability that two distinct gene copies of generation $t$ are identical by descent;
- the **variance effective size** $N_e^{(v)}$ is defined by $\operatorname{Var}(p_{t+1} \mid p_t) = \dfrac{p_t (1 - p_t)}{2 N_e^{(v)}}$, where $p_t$ is the allele frequency;
- the **eigenvalue effective size** $N_e^{(e)}$ is defined by $\lambda = 1 - \frac{1}{2 N_e^{(e)}}$, where $\lambda$ is the asymptotic multiplier of non-identity, the largest eigenvalue below $1$ of the linear recursion for the expected heterozygosity (or for the vector of non-identity probabilities). Ewens's eigenvalue effective size is defined instead from the leading non-unit eigenvalue of the transition matrix of the population's Markov chain; the two readings are not identified here.

For the diploid Wright–Fisher model with $2N$ gene copies all three equal $N$: two distinct copies come from the
same parental copy with probability $1/(2N)$, the binomial resampling of the
[Wright–Fisher matrix](../wright-fisher-markov-chain/wright-fisher.md) has conditional variance $p(1 - p)/(2N)$, and expected heterozygosity
[decays by the factor](../wright-fisher-markov-chain/sum-mat-pow-mul-heterozygosity.md) $1 - 1/(2N)$. In other models the three can differ, and the definitions apply
only where the stated recursion or conditional variance holds. For a model with $M$ gene copies per generation, haploid or diploid, the definitions are
read with $2N_e$ replaced by the number $M_e$ of gene copies of the comparison Wright–Fisher population; a
haploid Wright–Fisher population of $M$ genes has $M_e = M$, the same as $N_e = M/2$ diploids.

## Depends on

- [Neutral Wright–Fisher transition matrix](../wright-fisher-markov-chain/wright-fisher.md)
- [Geometric decay of heterozygosity under Wright–Fisher drift](../wright-fisher-markov-chain/sum-mat-pow-mul-heterozygosity.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.6 (effective population number as the size of an idealized population with the same rate of inbreeding or of increase of variance; inbreeding and variance effective numbers, after Crow (1954); the asymptotic multiplier of non-identity, Eq. (VI-28); Ewens's (1982) eigenvalue effective size as a rigorization of the variance effective number).
