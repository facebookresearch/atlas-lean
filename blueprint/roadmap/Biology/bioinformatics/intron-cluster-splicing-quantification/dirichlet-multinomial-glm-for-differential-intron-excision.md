# Dirichlet-multinomial GLM for differential intron excision

Fix an [intron cluster](intron-clusters-from-shared-splice-junctions.md) $C$ with $J \ge 2$ introns, intron counts $y_{ij}$ in sample $i$ with total $n_{iC} = \sum_{j} y_{ij}$, and a covariate row vector $x_i \in \mathbb{R}^P$. The **Dirichlet-multinomial GLM** is

$$(y_{i1}, \dots, y_{iJ}) \mid n_{iC} \sim \mathcal{DM}\big(n_{iC};\ \alpha_1 p_{i1}, \dots, \alpha_J p_{iJ}\big), \qquad p_{ij} = \frac{\exp(x_i\beta_j + \mu_j)}{\sum_{j'}\exp(x_i\beta_{j'} + \mu_{j'})},$$

with coefficient vectors $\beta_j \in \mathbb{R}^P$, intercepts $\mu_j$ and concentrations $\alpha_j > 0$, where for $a \in (0,\infty)^J$, $a_\cdot = \sum_j a_j$ and $y_\cdot = \sum_j y_j = n$,

$$\mathcal{DM}(y \mid n, a) = \binom{n}{y_1, \dots, y_J}\frac{\Gamma(a_\cdot)}{\Gamma(a_\cdot + y_\cdot)}\prod_{j=1}^{J}\frac{\Gamma(a_j + y_j)}{\Gamma(a_j)} .$$

Parameters are estimated by maximum likelihood with a weak $\mathrm{Gamma}(1 + 10^{-4}, 10^{-4})$ penalty on the concentrations.

**Multinomial limit.** Fix $n$. If parameters $a^{(t)} \in (0,\infty)^J$ satisfy $a^{(t)}_\cdot \to \infty$ and $a^{(t)}/a^{(t)}_\cdot \to q$, then $\mathcal{DM}(n, a^{(t)}) \to \mathrm{Multinomial}(n, q)$ (the [multinomial distribution](../../../Probability/distributions/discrete/multinomial-distribution/multinomial.md)) pointwise on count vectors. The limiting probabilities are the normalized parameters $q$, with $q_j \propto \lim \alpha_j p_j$, which differ from $p$ unless the ratios $\alpha_j/\alpha_k$ tend to $1$: with $p = (1/2, 1/2)$ and concentrations $(\alpha_1, \alpha_2) = (t, 2t)$, so $a = (t/2, t)$, the mean proportions $a/a_\cdot$ are $(1/3, 2/3)$ for every $t$, and so is the limit. For a common concentration, $a_j = \alpha p_j$ with $\alpha \to \infty$, the limit is $\mathrm{Multinomial}(n, p)$; smaller concentrations give more overdispersion of intron usage across samples than multinomial sampling allows.

**Differential splicing test.** For two groups of samples coded $x_i \in \{0, 1\}$, the source compares the intercept-only model with the model including $x$ and refers twice the log-likelihood difference to $\chi^2_{J-1}$. This is the source's reference test, not a consequence of Wilks' theorem established here (see below). The whole cluster is tested at once, rather than each intron separately.

## Depends on

- [Intron clusters from shared splice junctions](intron-clusters-from-shared-splice-junctions.md)
- [Multinomial distribution](../../../Probability/distributions/discrete/multinomial-distribution/multinomial.md)

## Expansion

The Dirichlet-multinomial is the compound law of $y \mid \pi \sim \mathrm{Multinomial}(n, \pi)$ and $\pi \sim \mathrm{Dirichlet}(a)$: integrating $\binom{n}{y}\prod_j \pi_j^{y_j}$ against $\frac{\Gamma(a_\cdot)}{\prod_j\Gamma(a_j)}\prod_j \pi_j^{a_j - 1}$ over the simplex gives $\binom{n}{y}\frac{\Gamma(a_\cdot)}{\prod_j\Gamma(a_j)}\cdot\frac{\prod_j\Gamma(a_j + y_j)}{\Gamma(a_\cdot + n)}$ by the Dirichlet integral. Its mean is $n\,a/a_\cdot$, and with $a = \alpha p$ for a common $\alpha$ the covariance is the multinomial covariance inflated by $(n + \alpha)/(1 + \alpha)$, which tends to $1$ as $\alpha \to \infty$. The softmax link identifies only differences of the $\beta_j$ and $\mu_j$ across introns, so counting softmax contrasts gives the alternative model with a binary covariate $J - 1$ more coefficients than the null; this count is where the $\chi^2_{J-1}$ reference comes from. It does not verify the regularity conditions of Wilks' theorem: the likelihood depends on the parameters only through the products $\alpha_j p_{ij}$, and under the null, where $p_{ij} = p_j$ does not depend on $i$, the intron-specific concentrations and the null proportions can change together with every product $\alpha_j p_j$ unchanged, so the null parameters are not identifiable.

## Sources

- Y. I. Li, D. A. Knowles, J. Humphrey, A. N. Barbeira, S. P. Dickinson, H. K. Im and J. K. Pritchard, "Annotation-free quantification of RNA splicing using LeafCutter", *Nature Genetics* 50 (2018), 151–158, Online Methods "Dirichlet-multinomial generalized linear model" and "Differential intron excision across conditions", <https://doi.org/10.1038/s41588-017-0004-9> (PMC5742080).
