# Dirichlet-multinomial GLM for differential intron excision

Fix an [intron cluster](intron-clusters-from-shared-splice-junctions.md) $C$ with $J \ge 2$ introns, intron counts $y_{ij}$ in sample $i$ with total $n_{iC} = \sum_{j} y_{ij}$, and a covariate row vector $x_i \in \mathbb{R}^P$. The **Dirichlet-multinomial GLM** is

$$(y_{i1}, \dots, y_{iJ}) \mid n_{iC} \sim \mathcal{DM}\big(n_{iC};\ \alpha_1 p_{i1}, \dots, \alpha_J p_{iJ}\big), \qquad p_{ij} = \frac{\exp(x_i\beta_j + \mu_j)}{\sum_{j'}\exp(x_i\beta_{j'} + \mu_{j'})},$$

with coefficient vectors $\beta_j \in \mathbb{R}^P$, intercepts $\mu_j$ and concentrations $\alpha_j > 0$, where for $a \in (0,\infty)^J$, $a_\cdot = \sum_j a_j$ and $y_\cdot = \sum_j y_j = n$,

$$\mathcal{DM}(y \mid n, a) = \binom{n}{y_1, \dots, y_J}\frac{\Gamma(a_\cdot)}{\Gamma(a_\cdot + y_\cdot)}\prod_{j=1}^{J}\frac{\Gamma(a_j + y_j)}{\Gamma(a_j)} .$$

Parameters are estimated by maximum likelihood with a weak $\mathrm{Gamma}(1 + 10^{-4}, 10^{-4})$ penalty on the concentrations.

**Overdispersion.** If $a_j = \alpha_j p_j$ with all $\alpha_j \to \infty$ at fixed $p$, then $\mathcal{DM}(n, a) \to \mathrm{Multinomial}(n, p)$; smaller $\alpha_j$ give more overdispersion of intron usage across samples than binomial or multinomial sampling allows.

**Differential splicing test.** For two groups of samples coded $x_i \in \{0, 1\}$, compare the intercept-only model with the model including $x$ by a likelihood-ratio test: twice the log-likelihood difference is referred to $\chi^2_{J-1}$. The whole cluster is tested at once, rather than each intron separately.

## Depends on

- [Intron clusters from shared splice junctions](intron-clusters-from-shared-splice-junctions.md)

## Expansion

The Dirichlet-multinomial is the compound law of $y \mid \pi \sim \mathrm{Multinomial}(n, \pi)$ and $\pi \sim \mathrm{Dirichlet}(a)$: integrating $\binom{n}{y}\prod_j \pi_j^{y_j}$ against $\frac{\Gamma(a_\cdot)}{\prod_j\Gamma(a_j)}\prod_j \pi_j^{a_j - 1}$ over the simplex gives $\binom{n}{y}\frac{\Gamma(a_\cdot)}{\prod_j\Gamma(a_j)}\cdot\frac{\prod_j\Gamma(a_j + y_j)}{\Gamma(a_\cdot + n)}$ by the Dirichlet integral. Its mean is $n\,a/a_\cdot$, and with $a = \alpha p$ for a common $\alpha$ the covariance is the multinomial covariance inflated by $(n + \alpha)/(1 + \alpha)$, which tends to $1$ as $\alpha \to \infty$. The softmax link identifies only differences of the $\beta_j$ and $\mu_j$ across introns, so the alternative model with a binary covariate has $J - 1$ more free parameters than the null, giving the $\chi^2_{J-1}$ reference by Wilks' theorem.

## Sources

- Y. I. Li, D. A. Knowles, J. Humphrey, A. N. Barbeira, S. P. Dickinson, H. K. Im and J. K. Pritchard, "Annotation-free quantification of RNA splicing using LeafCutter", *Nature Genetics* 50 (2018), 151–158, Online Methods "Dirichlet-multinomial generalized linear model" and "Differential intron excision across conditions", <https://doi.org/10.1038/s41588-017-0004-9> (PMC5742080).
