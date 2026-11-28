# Moment dynamics of ecDNA copy number under positive selection

In the [binomial segregation model](binomial-segregation-model-of-ecdna-and-neutral-moments.md), let cells carrying at least one ecDNA copy divide at rate $s$ and ecDNA-free cells at rate $1$, with $s > 1$ for positive selection. The densities $\rho_k = N_k/N$ satisfy

$$\frac{d\rho_k}{dt} = s\,\Big[-2\rho_k + 2\sum_{i \ge \lceil k/2\rceil,\, i\ge1} \rho_i\binom{2i}{k}2^{-2i}\Big] + (s-1)\rho_0\,\rho_k \quad (k \ge 1),$$

$$\frac{d\rho_0}{dt} = 2s\sum_{i \ge 1}\rho_i 4^{-i} - (s-1)(1-\rho_0)\rho_0 .$$

Here $(s-1)\rho_0\rho_k$ is the dilution correction from unequal growth rates. Assume the initial moments $M_l(0) = \sum_k k^l\rho_k(0)$ are finite for $l = 1, 2$. Then the moments $M_l = \sum_k k^l\rho_k$ satisfy

$$\frac{dM_1}{dt} = (s-1)\rho_0 M_1, \qquad M_1(t) = M_1(0)\exp\Big((s-1)\int_0^t \rho_0(\tau)\,d\tau\Big),$$

$$\frac{dM_2}{dt} = s M_1 + (s-1)\rho_0 M_2, \qquad M_2(t) = M_2(0)\,\frac{M_1(t)}{M_1(0)} + s\,t\,M_1(t),$$

where the closed form for $M_2$ assumes $M_1(0) > 0$, that is, some cell initially carries ecDNA. If $M_1(0) = 0$, every cell is initially ecDNA-free, $\rho_0 \equiv 1$ and $M_1 \equiv M_2 \equiv 0$.

At $s = 1$ these reduce to the neutral results. For $M_1(0) > 0$ the mean copy number grows, with relative growth rate $(s-1)\rho_0$: fast while ecDNA-free cells are common, slower as $\rho_0$ falls. The mean converges to a finite limit exactly when $\int_0^\infty \rho_0(\tau)\,d\tau < \infty$; a falling $\rho_0$ alone does not imply a plateau. In the two-population description started with some ecDNA-positive cells, ecDNA-positive cells take over the population, $f_+ \to 1$.

## Depends on

- [Binomial segregation model of ecDNA copy number and its neutral moments](binomial-segregation-model-of-ecdna-and-neutral-moments.md)

## Proof depends on

- [Second moment of the binomial law](../../../Probability/distributions/discrete/binomial-distribution/integral-sq-map-cast-binomial.md): with $n = 2i$ and $p = 1/2$, the second moment $i^2 + i/2$.

## Expansion

With unnormalized counts, $\sum_k k\,N_k$ grows at rate $s\sum_i iN_i$, because each division of a carrier conserves total copies in expectation and doubles them by replication. The total population grows at rate $\rho_0 + s(1 - \rho_0)$. Dividing gives $dM_1/dt = sM_1 - (\rho_0 + s - s\rho_0)M_1 = (s-1)\rho_0M_1$. The same bookkeeping with the binomial second moment $i^2 + i/2$ gives the $M_2$ equation. When $M_1(0) > 0$, $M_1(t) > 0$ for all $t$, and substituting $M_2 = c(t)M_1$ gives $c' = s$, $c(0) = M_2(0)/M_1(0)$. The paper writes the general moment equation as $dM_l/dt = s\,(dM_l/dt)|_{s=1} + (s-1)\rho_0M_l$. Its displayed second-moment equation drops the factor $s$ on $M_1$, which the general equation restores. The sign of the correction term in the $\rho_0$ equation is fixed by $\sum_k d\rho_k/dt = 0$; the paper's displayed $\rho_0$ equation carries the opposite sign. The paper also states the leading-order form $M_2 \approx t\,M_1$ (initial term dropped).

## Sources

- J. T. Lange, J. C. Rose, C. Y. Chen et al., "The evolutionary dynamics of extrachromosomal DNA in human cancers", *Nature Genetics* 54 (2022), <https://doi.org/10.1038/s41588-022-01177-x> (PMC9534767), Methods subsections "Deterministic two-population model with selection", "Stochastic dynamics of ecDNA under positive selection" and "Moment dynamics for ecDNA under positive selection".
