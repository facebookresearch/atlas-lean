# Binomial segregation model of ecDNA copy number and its neutral moments

Extrachromosomal DNA (ecDNA) elements lack centromeres and are split at random between daughter cells. Model a growing cell population in continuous time in which every cell divides at rate $1$, with time measured in generations. A dividing cell with $i$ ecDNA copies first replicates them to $2i$, and one daughter receives $k \sim \mathrm{Bin}(2i, 1/2)$ copies while the other receives $2i - k$. Cells with no ecDNA produce only ecDNA-free daughters.

Let $N_k(t)$ be the expected number of cells with $k$ copies, $N(t) = \sum_k N_k(t)$, and $\rho_k = N_k/N$. Then

$$\frac{dN_k}{dt} = -N_k + 2\sum_{i \ge \lceil k/2\rceil} N_i \binom{2i}{k} 2^{-2i}, \qquad \frac{d\rho_k}{dt} = -2\rho_k + 2\sum_{i \ge \lceil k/2\rceil} \rho_i \binom{2i}{k} 2^{-2i},$$

and $N(t) = N(0)e^{t}$. Let $M_l(t) = \sum_k k^l \rho_k(t)$ be the copy-number moments. Then:

- **Mean is conserved:** $M_1(t) = M_1(0)$.
- **Variance grows linearly:** $\dfrac{dM_2}{dt} = M_1$, so $M_2(t) = M_2(0) + M_1(0)\,t$ and $\operatorname{Var}(t) = \operatorname{Var}(0) + M_1(0)\,t$.
- More generally the paper reports that $M_l(t)$ grows like $t^{l-1}$.

Starting from one cell with one copy, $M_1 \equiv 1$ and $M_2(t) = 1 + t \approx t$. Under neutrality the mean copy number stays fixed while the copy-number distribution spreads and a growing fraction of cells loses ecDNA altogether. In a simplified two-population (ecDNA-positive versus ecDNA-free) description of neutral growth, the fraction of ecDNA-positive cells decays like $f_+(t) = 2/(2+t)$.

## Proof depends on

- [Second moment of the binomial law](../../../Probability/distributions/discrete/binomial-distribution/integral-sq-map-cast-binomial.md): with $n = 2i$ and $p = 1/2$, the second moment $i^2 + i/2$.

## Expansion

Each division removes one cell of type $i$ and adds two daughters, each with marginal law $\mathrm{Bin}(2i, 1/2)$; this gives the equation for $N_k$. Summing over $k$ gives $dN/dt = N$, and dividing by $N$ gives the density equation. For the moments, a $\mathrm{Bin}(2i, 1/2)$ variable has mean $i$ and second moment $i^2 + i/2$. Hence $\sum_k k\,(d\rho_k/dt) = -2M_1 + 2M_1 = 0$, and $\sum_k k^2 (d\rho_k/dt) = -2M_2 + 2(M_2 + M_1/2) = M_1$. Random segregation is the source of the linear-in-time variance; an equal split would keep every cell at its starting copy number. The paper checks these predictions against stochastic Gillespie simulations, live-cell imaging of segregation and single-cell copy-number distributions.

## Sources

- J. T. Lange, J. C. Rose, C. Y. Chen et al., "The evolutionary dynamics of extrachromosomal DNA in human cancers", *Nature Genetics* 54 (2022), <https://doi.org/10.1038/s41588-022-01177-x> (PMC9534767), Methods subsections "Stochastic simulations of ecDNA population dynamics", "Deterministic two-population model without selection", "Stochastic dynamics of neutral ecDNA" and "Moment dynamics for neutral ecDNA copies".
