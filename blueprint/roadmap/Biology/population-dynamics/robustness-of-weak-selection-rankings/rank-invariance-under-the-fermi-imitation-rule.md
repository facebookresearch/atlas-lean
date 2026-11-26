# Rank invariance of strategy abundance under the Fermi imitation rule

**Model.** A well-mixed population of $N$ individuals plays a game with strategies $1, \dots, d$. In the pairwise comparison (imitation) process, a random focal individual with payoff $\pi_f$ compares itself with a random model individual with payoff $\pi_m$ and adopts the model's strategy with probability $f\big(\beta(\pi_m - \pi_f)\big)$, where $\beta \ge 0$ is the selection intensity and $f : \mathbb R \to [0,1]$ is a strictly increasing imitation function with $f(0) > 0$. Mutations are rare, so the population is almost always monomorphic and the long-run dynamics is the embedded Markov chain on the $d$ monomorphic states whose transition rates are proportional to fixation probabilities $\rho_{ij}(\beta)$ of a single $i$-mutant in a resident $j$ population. The stationary distribution of this chain ranks strategies by abundance.

**Two strategies.** For $d = 2$ let $\Delta\pi_j = \pi_1(j) - \pi_2(j)$ be the payoff difference when $j$ individuals play strategy 1. The abundance of strategy 1 exceeds that of strategy 2 iff $\rho_{12} > \rho_{21}$, and

$$\frac{\rho_{12}}{\rho_{21}} = \prod_{j=1}^{N-1} \frac{f(\beta\,\Delta\pi_j)}{f(-\beta\,\Delta\pi_j)} .$$

**Proposition (Fermi rule).** If $f(x) = 1/(1 + e^{-x})$, then $f(x)/f(-x) = e^{x}$ and

$$\frac{\rho_{12}}{\rho_{21}} = \exp\Big(\beta \sum_{j=1}^{N-1} \Delta\pi_j\Big),$$

so for every $\beta > 0$ strategy 1 is more abundant iff $\sum_{j=1}^{N-1}\Delta\pi_j > 0$. The ranking obtained under weak selection ($\beta \to 0$) is therefore the ranking for every selection intensity, for any two-strategy game, pairwise or multiplayer.

**Failure in general.** For other strictly increasing imitation functions (for example a rescaled error function), the ratio $f(x)/f(-x)$ is not an exponential, the sign of $\log(\rho_{12}/\rho_{21}) = \sum_j \log\{f(\beta\Delta\pi_j)/f(-\beta\Delta\pi_j)\}$ can change with $\beta$ in multiplayer two-strategy games, and the weak-selection criterion differs from the strong-selection one. With three strategies, for any strictly increasing twice-differentiable $f$ and large enough $N$, there are $3 \times 3$ payoff matrices whose stationary abundances coincide in the weak- and strong-selection limits but in which at least two strategies change rank at an intermediate selection intensity; in random games with Gaussian or uniform payoff entries such rank changes are common.

## Expansion

For a birth–death chain on $j \in \{0, \dots, N\}$ with transition ratio $T^-_j/T^+_j = f(-\beta\Delta\pi_j)/f(\beta\Delta\pi_j)$, the fixation probability of a single mutant is $\rho = \big(1 + \sum_{k=1}^{N-1}\prod_{j=1}^{k} T^-_j/T^+_j\big)^{-1}$, and the ratio of the two fixation probabilities telescopes to the product above. With two monomorphic states the stationary distribution is $(\rho_{12}, \rho_{21})/(\rho_{12}+\rho_{21})$. The Fermi identity turns the product into an exponential of a $\beta$-independent sum. For $d \ge 3$ the stationary distribution is a rational function of all pairwise fixation probabilities, so no single sign controls the ranking; the construction exploits that when numerator and denominator products both tend to $0$ as $\beta$ grows, derivatives of $f$ far from $0$ decide the comparison.

## Sources

- B. Wu, J. García, C. Hauert, A. Traulsen, "Extrapolating weak selection in evolutionary games", PLoS Computational Biology 9 (2013) e1003381, Results ("Games with two strategies", Figure 2; "Games with three strategies", Theorem 1 with proof by construction in the Supporting Information, Section 4; random games, Figure 3) and Methods (embedded Markov chain under rare mutations), <https://doi.org/10.1371/journal.pcbi.1003381> (PMC3854678).
