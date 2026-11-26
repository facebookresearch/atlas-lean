# Proportional likelihood with censored normal signals and a Beta mixture

In the setting of the
[categorical likelihood](categorical-likelihood-for-complexity-of-infection-and-allele-frequencies.md),
suppose each assay reports signal intensities $A_{1,ij}, A_{2,ij} \ge 0$ for the major and minor
alleles, and let $S^O_{ij} = A_{1,ij}/(A_{1,ij} + A_{2,ij})$ be the observed major-allele
proportion, censored to $[0,1]$. The true within-host major-allele frequency $S^T_{ij}$ has a
mixed distribution with point masses and a continuous part,

$$g(S^T_{ij} \mid m_i, p_j) =
\begin{cases}
(1-p_j)^{m_i} & S^T_{ij} = 0,\\
\big(1 - p_j^{m_i} - (1-p_j)^{m_i}\big)\,\mathrm{Beta}\big(S^T_{ij};\, \alpha_{m_i p_j}, \beta_{m_i p_j}\big) & 0 < S^T_{ij} < 1,\\
p_j^{m_i} & S^T_{ij} = 1,
\end{cases}$$

where the Beta parameters are fitted in advance to simulated mixtures in which each of the $m_i$
lineages carries the major allele with probability $p_j$ and lineage proportions are the spacings
of $m_i - 1$ sorted uniform variables. The observation is normal with mean $S^T_{ij}$ and variance
$\sigma^2_{ij}$ decreasing in the total signal intensity (scaled by an error level
$\varepsilon_{\mathrm{est}}$), censored at $0$ and $1$:

$$f(S^O_{ij} \mid S^T_{ij}) =
\begin{cases}
\Phi\!\big(-S^T_{ij}/\sigma_{ij}\big) & S^O_{ij} = 0,\\
\sigma_{ij}^{-1}\,\phi\!\big((S^O_{ij} - S^T_{ij})/\sigma_{ij}\big) & 0 < S^O_{ij} < 1,\\
\Phi\!\big((S^T_{ij} - 1)/\sigma_{ij}\big) & S^O_{ij} = 1,
\end{cases}$$

with $\Phi$ and $\phi$ the standard normal distribution and density functions. The likelihood is

$$L(M, P \mid S^O) = \prod_{i=1}^{n}\prod_{j=1}^{k}\Big[ f(S^O_{ij}\mid 0)\, g(0 \mid m_i,p_j)
+ \int_0^1 f(S^O_{ij}\mid s)\, g(s \mid m_i,p_j)\, ds + f(S^O_{ij}\mid 1)\, g(1 \mid m_i,p_j)\Big],$$

where the integral runs over the continuous part of $g$; $M$, $P$ and the latent $S^T$ are
sampled by Metropolis–Hastings under uniform priors.

## Depends on

- [Categorical likelihood for complexity of infection and allele frequencies](categorical-likelihood-for-complexity-of-infection-and-allele-frequencies.md)

## Expansion

The point masses of $g$ at $0$ and $1$ are the probabilities that all lineages share the minor or
the major allele, exactly as in the categorical model; when lineages differ, the within-host
frequency is a random mixture whose distribution depends on $m_i$ and $p_j$ and is approximated
by a fitted Beta density. For $m_i = 2$ the mixing proportion is uniform on $(0,1)$, so the
heterozygous signal can sit anywhere in the interval. Censoring the normal measurement model at the
boundaries assigns observed proportions of exactly $0$ or $1$ the tail probabilities of the normal
error, so that a monogenomic-looking call is still compatible with a minor lineage below detection.
Using the quantitative signal rather than thresholded calls keeps information about the relative
abundance of lineages.

## Sources

- H.-H. Chang, C. J. Worby, A. Yeka, J. Nankabirwa, M. R. Kamya, S. G. Staedke, G. Dorsey,
  M. Murphy, D. E. Neafsey, A. E. Jeffreys, C. Hubbart, et al., "THE REAL McCOIL: A method for the
  concurrent estimation of the complexity of infection and SNP allele frequency for malaria
  parasites", PLoS Computational Biology 13 (2017) e1005348, Materials and Methods,
  "Proportional method" (Eqs. 3-5), <https://doi.org/10.1371/journal.pcbi.1005348> (PMC5300274).
