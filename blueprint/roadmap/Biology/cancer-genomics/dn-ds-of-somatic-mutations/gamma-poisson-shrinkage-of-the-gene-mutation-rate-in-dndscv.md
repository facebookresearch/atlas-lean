# Gamma-Poisson shrinkage of the gene mutation rate in dNdScv

In the [Poisson dN/dS model](poisson-dn-ds-model-with-trinucleotide-substitution-rates.md), give each
gene $j$ its own substitution density $t_j$. Let $n_{s,j} = \sum_i n_{i,s,j}$ be its synonymous
count and $E_{s,j} = t \sum_i r_i L_{i,s,j}$ its expected synonymous count under a common density
$t$. The **dNdScv** background model assumes

$$n_{s,j} \mid \lambda_j \sim \mathrm{Poisson}(\lambda_j), \qquad \lambda_j \sim \mathrm{Gamma}(\alpha, \beta_j)
\quad (\text{shape } \alpha,\ \text{rate } \beta_j),$$

so that marginally $n_{s,j}$ is negative binomial, and fits it by a negative binomial regression of
$n_{s,j}$ on gene-level covariates with offset $\log E_{s,j}$. With $\mu_j$ the regression
prediction and $\theta$ the fitted overdispersion, $\alpha = \theta$ and $\beta_j = \theta / \mu_j$. The
gene's rate is then estimated from the joint likelihood
$L(t_j) = L_{\mathrm{Poisson}}(t_j \mid n_{s,j})\, L_{\mathrm{Gamma}}(t_j \mid \alpha, \beta_j)$, whose
maximizer over $t_j \ge 0$, expressed as an expected synonymous count, is

$$\widehat{E'_{s,j}} \;=\; \hat t_j \sum_i r_i L_{i,s,j} \;=\; \frac{n_{s,j} + \alpha - 1}{1 + \beta_j} \qquad \text{when } n_{s,j} + \alpha \ge 1,$$

which is $0$ when $n_{s,j} + \alpha = 1$. When $n_{s,j} + \alpha < 1$ (possible only for $n_{s,j} = 0$ and $\alpha < 1$), the joint likelihood increases without bound as $t_j \to 0$, so it has no maximizer with $t_j > 0$, the displayed formula would be negative, and the estimate is the boundary value $\widehat{E'_{s,j}} = 0$. This interpolates between the regression prediction (small $n_{s,j}$, gamma term dominant) and the
gene-local estimate $n_{s,j}$ (large counts, Poisson term dominant). Selection on gene $j$ is tested
by likelihood ratio tests on its $\omega_k$ with $t_j$ handled under this constraint, and confidence
intervals for $\omega_k$ come from the profile likelihood integrating out $t_j$.

## Depends on

- [Poisson dN/dS model with trinucleotide substitution rates](poisson-dn-ds-model-with-trinucleotide-substitution-rates.md)

## Remarks

As a function of $\lambda_j$, the product of the Poisson likelihood $\lambda_j^{n} e^{-\lambda_j}$ and
the gamma density $\lambda_j^{\alpha-1} e^{-\beta_j \lambda_j}$ is proportional to a
$\mathrm{Gamma}(n + \alpha,\ 1 + \beta_j)$ density, whose mode is $(n + \alpha - 1)/(1 + \beta_j)$ for $n + \alpha \ge 1$; for shape
$n + \alpha < 1$ the density is decreasing and unbounded near $0$, so its supremum is approached at the
boundary. Covariates (here the first 20 principal components of
169 epigenomic tracks) reduce the unexplained variation of rates across genes, hence $1/\theta$,
which sharpens the gamma constraint and raises power in small cohorts, while the remaining
overdispersion protects specificity. A model with one shared $t$ (uniform rates) inflates false
positives in large cohorts; a fully local $t_j$ lacks power in small ones; dNdScv adapts between the
two.

## Sources

- I. Martincorena, K. M. Raine, M. Gerstung et al., "Universal Patterns of Selection in Cancer and Somatic Tissues", *Cell* 171 (2017), <https://doi.org/10.1016/j.cell.2017.09.042> (PMC5720395), STAR Methods, subsection "Modeling variable mutation rates across genes: dNdScv".
