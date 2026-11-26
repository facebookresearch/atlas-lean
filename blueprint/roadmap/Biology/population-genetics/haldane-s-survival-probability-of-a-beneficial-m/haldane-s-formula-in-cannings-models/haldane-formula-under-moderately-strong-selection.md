# Haldane's formula in Dirichlet-type Cannings models under moderately strong selection

Let $N$ be the population size and let $Y_1, \dots, Y_N$ be independent copies of a random variable $Y$ with $P(Y > 0) = 1$ and $E\, e^{hY} < \infty$ for some $h > 0$. Form the exchangeable **Dirichlet-type paintbox**

$$W_i^{(N)} = \frac{Y_i}{\sum_{\ell=1}^N Y_\ell}, \qquad i = 1, \dots, N,$$

drawn independently in each generation. Each individual is either *beneficial* or *wildtype*; a wildtype individual has its weight reduced to $(1 - s_N) W_i$, a beneficial one keeps $W_i$. Each of the $N$ children of the next generation independently picks its parent with probability proportional to these modified weights and inherits the parent's type. Given $W$ and $k$ beneficial individuals, the number of beneficial individuals in the next generation is therefore

$$\mathrm{Bin}\!\left(N,\ \frac{\sum_{i \le k} W_i}{\sum_{i \le k} W_i + (1 - s_N)\sum_{i > k} W_i}\right).$$

Let $\rho^2 = E[Y^2]/E[Y]^2$, the limit of the neutral offspring variance $\operatorname{Var}\nu_1^{(N)}$ as $N \to \infty$.

**Theorem (moderately strong selection).** Fix $\eta \in (0, \tfrac14)$ and suppose

$$N^{-\frac12 + \eta} \le s_N \le N^{-\eta}.$$

Let $X_0 = 1$ be a single beneficial mutant and $\tau = \inf\{g \ge 0 : X_g \in \{0, N\}\}$. Then the fixation probability satisfies

$$P(X_\tau = N) \sim \frac{2 s_N}{\rho^2}, \qquad N \to \infty.$$

The case $Y \equiv$ const gives the Wright–Fisher model ($\rho^2 = 1$, fixation probability $\sim 2 s_N$); $Y \sim \mathrm{Gamma}(\kappa)$ gives a Dirichlet$(\kappa, \dots, \kappa)$ paintbox with $\rho^2 = 1 + 1/\kappa$.

## Depends on

- [Haldane's approximation for the survival probability of a branching mutant](../tendsto-survival-prob-div.md)
- [Cannings model of a haploid population](../../../coalescent-theory/multiple-merger-coalescents/cannings-models/cannings-model.md)

## Expansion

The proof follows the beneficial count through three phases. While $X_g \le N^{b+\delta}$ with $b = -\ln s_N / \ln N$ and $b + \delta < \tfrac12$, the mixed-binomial transition is sandwiched between two slightly supercritical Galton–Watson processes (a mixed-Poisson upper bound with random parameter about $(1 + s_N)\sum_{\ell \le k} Y_\ell / N$, and a truncated mixed-binomial lower bound), each with offspring mean $1 + s_N + o(s_N)$ and variance $\rho^2 + o(1)$; their survival probabilities are $2 s_N/\rho^2\,(1+o(1))$, which is Proposition 1 of the source. In the middle phase the drift of order $s_N X_g$ dominates the resampling noise of order $\sqrt{X_g}$ precisely because $s_N \gg N^{-1/2}$, so the frequency rises to a macroscopic level with probability $1 - o(1)$; a symmetric argument for the wildtype then finishes fixation. The lower bound $s_N \ge N^{-1/2+\eta}$ is where the method needs moderately strong selection; the complementary regime $\tfrac12 < b < 1$ is handled by an ancestral-selection-graph duality, and $b = \tfrac12$ remains open.

## Sources

- F. Boenkost, A. González Casanova, C. Pokalyuk, A. Wakolbinger, *Haldane's formula in Cannings models: the case of moderately strong selection*, J. Math. Biol. 83 (2021), 70 (Definition 1, Eqs. (7), (8), (10), (12), Theorem 1, Proposition 1). <https://doi.org/10.1007/s00285-021-01698-9> (PMCID: PMC8648686)
