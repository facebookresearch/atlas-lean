# Explicit skew-offspring models and their Λ-coalescent limits

Two explicit population models have multiple-merger coalescent limits.

In the Galton–Watson sampling model of Schweinsberg (2003), as presented by Berestycki (2009, Section 3.2.1), each of $N$ individuals has an independent number $X$ of offspring with $P(X > x) \sim Cx^{-\alpha}$ for some $\alpha \ge 1$ and $C > 0$ (assumption (75)), with $1 < E[X] < \infty$ when $\alpha > 1$, and $N$ of the offspring are chosen at random to form the next generation. This is a Cannings model, and with $c_N = E[\nu_1(\nu_1 - 1)]/(N - 1)$ the pair coalescence probability (equation (77)), Berestycki's Theorem 3.8 states that the ancestral partition of a sample of size $n$, run at time scale $1/c_N$, converges to Kingman's $n$-coalescent if $\alpha \ge 2$ and to the restriction to $\{1, \dots, n\}$ of the Beta-coalescent with parameter $\alpha$, the $\Lambda$-coalescent with $\Lambda = \mathrm{Beta}(2 - \alpha, \alpha)$ (his Example 3), if $1 \le \alpha < 2$; the case $\alpha = 1$ is the Bolthausen–Sznitman coalescent.

In the modified Moran model of Eldon and Wakeley (2006, Equation 7), at each step one parent reproduces; with probability $1 - N^{-\gamma}$ it has the usual Moran offspring, and with probability $N^{-\gamma}$ it and its offspring replace a fraction $\psi \in (0, 1]$ of the population, $\gamma > 0$. With time scaled by $\psi^2$ divided by the pair coalescence probability, the limit is the $\Lambda$-coalescent with $\Lambda = \delta_\psi$ for $0 < \gamma < 2$, the $\Lambda$-coalescent with mass $2/(2 + \psi^2)$ at $0$ and $\psi^2/(2 + \psi^2)$ at $\psi$ for $\gamma = 2$, and Kingman's coalescent for $\gamma > 2$ (their Model section and Table 1).

## Depends on

- [Möhle–Sagitov conditions for a Λ-coalescent limit](../../../../Biology/coalescent-theory/multiple-merger-coalescents/coalescent-limits-of-cannings-models/mohle-sagitov-lambda.md)
- [Möhle–Sagitov limit of the lineage count of Cannings models](../../../../Biology/coalescent-theory/multiple-merger-coalescents/coalescent-limits-of-cannings-models/tendsto-lineage-matrix-pow.md)
- [The Beta-coalescent measure on the unit interval](../../../../Biology/coalescent-theory/multiple-merger-coalescents/merger-rates-and-beta-coalescents/beta-lambda.md)
- [The α = 1 Beta-coalescent measure is the uniform measure](../../../../Biology/coalescent-theory/multiple-merger-coalescents/merger-rates-and-beta-coalescents/beta-lambda-one.md)

## Expansion

1. The Galton–Watson sampling model as an exchangeable Cannings model, and the asymptotics of $c_N$ in the three regimes $\alpha \ge 2$, $1 < \alpha < 2$ and $\alpha = 1$.
2. The rate of large families: the probability of a family of fraction at least $x$ of the next generation, compared with the rate $x^{-\alpha}(1 - x)^{\alpha}/(\alpha\Gamma(\alpha)\Gamma(2 - \alpha))$ of such mergers in the Beta-coalescent, as in Schweinsberg's sketch of the proof.
3. Verification of the limit conditions for the Galton–Watson model and identification of $\Lambda$.
4. The Eldon–Wakeley model: the pair and $x$-merger probabilities, the time scale with the factor $\psi^2$, and the three limits according to $\gamma$.

## Sources

- N. Berestycki, *Recent Progress in Coalescent Theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática, 2009, Section 3.2.1 (assumption (75), equation (77), Theorem 3.8) and Example 3. <https://arxiv.org/abs/0909.3985>
- J. Schweinsberg, Modeling the genealogy of populations using coalescents with multiple mergers, lecture slides, University of California at San Diego.
- Original result: J. Schweinsberg, Coalescent processes obtained from supercritical Galton–Watson processes, Stochastic Process. Appl. 106 (2003), 107–139. <https://doi.org/10.1016/s0304-4149(03)00028-0> The limit theorem follows Berestycki (2009, Theorem 3.8).
- B. Eldon and J. Wakeley, Coalescent processes when the distribution of offspring number among individuals is highly skewed, Genetics 172 (2006), 2621–2633, Model (Equation 7) and Table 1. <https://doi.org/10.1534/genetics.105.052175>
