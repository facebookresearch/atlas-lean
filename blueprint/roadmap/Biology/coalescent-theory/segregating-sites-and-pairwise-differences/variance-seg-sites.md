# Variance of the number of segregating sites

Let $\mu$ be a probability measure on a measurable space $(\Omega, \mathcal{F})$, let $(T_k)$ be Kingman holding times of a sample of size $n$ under $\mu$, with total branch length $L$, and let $\mathcal{G} \subseteq \mathcal{F}$ be a sub-σ-algebra. Let $\theta$ be a real number and $S$ a square-integrable real random variable whose conditional mean and conditional variance given $\mathcal{G}$ both equal $\frac{\theta}{2} L$ almost surely, as for a Poisson count with mean $\theta L/2$. Then

$$\operatorname{Var}(S) = \theta\, a_1(n) + \theta^2 a_2(n),$$

where $a_1(n) = \sum_{i=1}^{n-1} 1/i$ and $a_2(n) = \sum_{i=1}^{n-1} 1/i^2$ are [Tajima's constants](tajima-a1.md).

## Sources

- G. A. Watterson, *On the number of segregating sites in genetical models without recombination*, Theoret. Population Biol. 7 (1975), 256–276.
- F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA polymorphism*, Genetics 123 (1989), 585–595.
