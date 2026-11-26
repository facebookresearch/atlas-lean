# Moment dynamics of ecDNA copy number under positive selection

In the [binomial segregation model](binomial-segregation-model-of-ecdna-and-neutral-moments.md), let cells carrying at least one ecDNA copy divide at rate $s$ and ecDNA-free cells at rate $1$, with $s > 1$ for positive selection. The densities $\rho_k = N_k/N$ satisfy

$$\frac{d\rho_k}{dt} = s\,\Big[-2\rho_k + 2\sum_{i \ge \lceil k/2\rceil,\, i\ge1} \rho_i\binom{2i}{k}2^{-2i}\Big] + (s-1)\rho_0\,\rho_k \quad (k \ge 1),$$

$$\frac{d\rho_0}{dt} = 2s\sum_{i \ge 1}\rho_i 4^{-i} - (s-1)(1-\rho_0)\rho_0 .$$

Here $(s-1)\rho_0\rho_k$ is the dilution correction from unequal growth rates. For the moments $M_l = \sum_k k^l\rho_k$ with $l \ge 1$:

$$\frac{dM_1}{dt} = (s-1)\rho_0 M_1, \qquad M_1(t) = M_1(0)\exp\Big((s-1)\int_0^t \rho_0(\tau)\,d\tau\Big),$$

$$\frac{dM_2}{dt} = s M_1 + (s-1)\rho_0 M_2, \qquad M_2(t) = \Big(\frac{M_2(0)}{M_1(0)} + s\,t\Big)M_1(t).$$

At $s = 1$ these reduce to the neutral results. The mean copy number grows while ecDNA-free cells are common. As $\rho_0$ falls the growth slows, and the mean levels off. In the two-population description, ecDNA-positive cells take over the population, $f_+ \to 1$.

## Depends on

- [Binomial segregation model of ecDNA copy number and its neutral moments](binomial-segregation-model-of-ecdna-and-neutral-moments.md)

## Expansion

With unnormalized counts, $\sum_k k\,N_k$ grows at rate $s\sum_i iN_i$, because each division of a carrier conserves total copies in expectation and doubles them by replication. The total population grows at rate $\rho_0 + s(1 - \rho_0)$. Dividing gives $dM_1/dt = sM_1 - (\rho_0 + s - s\rho_0)M_1 = (s-1)\rho_0M_1$. The same bookkeeping with the binomial second moment $i^2 + i/2$ gives the $M_2$ equation, and substituting $M_2 = c(t)M_1$ gives $c' = s$. The paper writes the general moment equation as $dM_l/dt = s\,(dM_l/dt)|_{s=1} + (s-1)\rho_0M_l$. Its displayed second-moment equation drops the factor $s$ on $M_1$, which the general equation restores. The sign of the correction term in the $\rho_0$ equation is fixed by $\sum_k d\rho_k/dt = 0$; the paper's displayed $\rho_0$ equation carries the opposite sign. The paper also states the leading-order form $M_2 \approx t\,M_1$ (initial term dropped).

## Sources

- J. T. Lange, J. C. Rose, C. Y. Chen et al., "The evolutionary dynamics of extrachromosomal DNA in human cancers", *Nature Genetics* 54 (2022), <https://doi.org/10.1038/s41588-022-01177-x> (PMC9534767), Methods subsections "Deterministic two-population model with selection", "Stochastic dynamics of ecDNA under positive selection" and "Moment dynamics for ecDNA under positive selection".
