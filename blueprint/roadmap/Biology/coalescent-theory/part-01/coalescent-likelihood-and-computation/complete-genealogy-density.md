# The density of a complete coalescent genealogy

For Kingman's coalescent on $n$ labelled lineages, a complete genealogy consists of a ranked labelled history, the sequence of merging pairs, and the holding times $t_n, \dots, t_2$, where $t_k$ is the time with $k$ lineages. The jump chain chooses each of the $\binom k2$ pairs with probability $1/\binom k2$, independently of the holding times, and the holding time with $k$ lineages is exponential with rate $\binom k2$; so a given ranked labelled history with given holding times has density

$$\prod_{k=2}^n \frac{1}{\binom k2}\cdot \binom k2 e^{-\binom k2 t_k} = \prod_{k=2}^n e^{-\binom k2 t_k},$$

each specified merger contributing rate $1$ and each interval its survival factor, and the $\prod_{k=2}^n \binom k2$ ranked labelled histories have equal probability. Under a variable population size with positive, locally integrable intensity $\lambda = 1/f$ and integrated intensity $\Lambda$ satisfying $\Lambda(t) \to \infty$ as $t \to \infty$ (Tavaré 2004, Section 2.4), the holding times have the density given by the [heterochronous Λ-coalescent likelihood](../../multiple-merger-coalescents/multiple-merger-coalescent-inference-of-effective-population-size/heterochronous-lambda-coalescent-likelihood-with-variable-effective-population-size.md) with merger measure $\delta_0$ (Kingman's coalescent), a single sampling time and $N_e = f$, and the jump chain is unchanged, so, in the partial sums $s_j = t_n + \dots + t_j$, $s_{n+1} = 0$, the density of a ranked labelled history with times is $\prod_{j=2}^n \lambda(s_j)\exp\bigl(-\binom j2(\Lambda(s_j) - \Lambda(s_{j+1}))\bigr)$. If instead $\Lambda$ is bounded, the same expressions are only subdensities: for $f(t) = e^t$ and $n = 2$ the holding-time density $e^{-t}\exp(-(1 - e^{-t}))$ has total mass $1 - e^{-1}$, and the remaining mass belongs to a genealogy that never completes. Summing over the rankings compatible with a labelled tree gives the density of the unranked labelled tree, which differs by the number of such rankings; the corresponding summation over labellings, for ranked unlabelled trees, is the [density of a Tajima's genealogy under a variable population size](../../ranked-labeled-histories-of-coalescent-trees/tajima-genealogies/tajima-genealogy-density-under-a-variable-population-size.md).

## Depends on

- [Heterochronous Λ-coalescent likelihood with variable effective population size](../../multiple-merger-coalescents/multiple-merger-coalescent-inference-of-effective-population-size/heterochronous-lambda-coalescent-likelihood-with-variable-effective-population-size.md)
- [Clock and epoch lengths of the variable-size coalescent](../../site-frequency-spectrum-under-variable-populatio/deterministic-coalescent-time-change.md)
- [Number of ranked labeled histories](../../ranked-labeled-histories-of-coalescent-trees/card-ranked-history.md)
- [Log-likelihood of one coalescent interval in the skyline model](../../skyline-plot-estimates-of-population-size/skyline-log-lik.md)

## Expansion

1. The density of a ranked labelled history with holding times, from the independence of the jump chain and the holding times.
2. The variable-size density of a ranked labelled history from the holding-time density under an unbounded cumulative rate, its form for piecewise-constant sizes, and the subdensity with mass at infinity when the cumulative rate is bounded.
3. Densities of unranked labelled trees by summation over compatible rankings.

## Sources

- S. Tavaré, Ancestral inference in population genetics, in *Lectures on Probability Theory and Statistics*, Lecture Notes in Math. 1837, Springer, 2004, 1–188, Section 2.4, equation (2.4.6).
