# The density of a complete coalescent genealogy

For Kingman's coalescent on $n$ labelled lineages, a complete genealogy consists of a ranked labelled history, the sequence of merging pairs, and the holding times $t_n, \dots, t_2$, where $t_k$ is the time with $k$ lineages. The jump chain chooses each of the $\binom k2$ pairs with probability $1/\binom k2$, independently of the holding times, and the holding time with $k$ lineages is exponential with rate $\binom k2$; so a given ranked labelled history with given holding times has density

$$\prod_{k=2}^n \frac{1}{\binom k2}\cdot \binom k2 e^{-\binom k2 t_k} = \prod_{k=2}^n e^{-\binom k2 t_k},$$

each specified merger contributing rate $1$ and each interval its survival factor, and the $\prod_{k=2}^n \binom k2$ ranked labelled histories have equal probability. Under a variable population size with intensity $\lambda = 1/f$ and integrated intensity $\Lambda$, the holding times have the joint density $\prod_{j=2}^n \binom j2 \lambda(s_j)\exp\bigl(-\binom j2(\Lambda(s_j) - \Lambda(s_{j+1}))\bigr)$ in the partial sums $s_j = t_n + \dots + t_j$, $s_{n+1} = 0$ (Tavaré 2004, equation (2.4.6)), and the jump chain is unchanged, so the density of a ranked labelled history with times is $\prod_{j=2}^n \lambda(s_j)\exp\bigl(-\binom j2(\Lambda(s_j) - \Lambda(s_{j+1}))\bigr)$. Summing over the rankings and labellings compatible with a tree gives the densities of unranked or unlabelled trees, which differ by the number of such rankings and labellings.

## Depends on

- [Clock and epoch lengths of the variable-size coalescent](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/deterministic-coalescent-time-change.md)
- [Number of ranked labeled histories](../../../Biology/coalescent-theory/ranked-labeled-histories-of-coalescent-trees/card-ranked-history.md)
- [Log-likelihood of one coalescent interval in the skyline model](../../../Biology/coalescent-theory/skyline-plot-estimates-of-population-size/skyline-log-lik.md)

## Expansion

1. The density of a ranked labelled history with holding times, from the independence of the jump chain and the holding times.
2. The variable-size density from (2.4.6), and its form for piecewise-constant sizes.
3. Densities of unranked and unlabelled trees by summation over compatible rankings and labellings.
4. Serial sampling, in which lineages enter at fixed times, as a separate statement.

## Sources

- S. Tavaré, Ancestral inference in population genetics, in *Lectures on Probability Theory and Statistics*, Lecture Notes in Math. 1837, Springer, 2004, 1–188, Section 2.4, equation (2.4.6).
