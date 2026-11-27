# Collapsed-data MLE of haplotype frequencies from pooled genotypes

**Setting.** Haplotypes over $L$ diallelic loci are vectors $y\in\Omega = \{0,1\}^L$ with population frequencies $f(y)$, where $0$ is the ancestral haplotype with no variant. There are $n$ pools, each of $k$ diploid individuals, so a pool holds $K = 2k$ independent haplotypes $Y_{i1},\dots,Y_{iK}$. Only the pool totals $T_i = \sum_{j=1}^K Y_{ij}$ are observed. The collapsed data keep only whether each allele count is zero:

$$Z_i = \Big(\mathbb{1}\{T_{1i}\ge 1\},\dots,\mathbb{1}\{T_{Li}\ge 1\}\Big),$$

as in group testing. Let $g$ be the law of $Z_i$, and for a set of loci $\Lambda$ let $f_0(\Lambda) = \mathbb{P}(Y_{lij} = 0,\ l\in\Lambda)$ and $g_0(\Lambda) = \mathbb{P}(Z_{li} = 0,\ l\in\Lambda)$.

**Estimator.** Since all $K$ haplotypes must carry $0$ at every locus of $\Lambda$, $g_0(\Lambda) = f_0(\Lambda)^K$. The collapsed-data MLE of $g_0(\Lambda)$ is the proportion $n_{Z0}(\Lambda)/n$ of pools with zero counts at all loci of $\Lambda$, and inclusion-exclusion gives the collapsed-data MLE of each haplotype frequency:

$$\hat f_{CD}(y) = \Big(\frac{n_{Z0}(\Lambda(y))}{n}\Big)^{1/K} + \sum_{r=1}^{m}(-1)^r\sum_{\substack{S\subset\Lambda'(y)\\|S| = r}}\Big(\frac{n_{Z0}(\Lambda(y)\cup S)}{n}\Big)^{1/K},$$

where $\Lambda(y) = \{l: y_l = 0\}$, $\Lambda'(y) = \{l: y_l = 1\}$ and $m = |\Lambda'(y)|$.

## Expansion

$\mathbb{P}(Y = y)$ is the probability that the haplotype is $0$ on $\Lambda(y)$ minus the probability that it is also $0$ at one or more loci of $\Lambda'(y)$, which is the inclusion-exclusion sum over $f_0(\Lambda(y)\cup S)$; each such term is the $K$-th root of a zero-pattern probability of the collapsed data, estimated by a sample proportion. The estimator is positive only for haplotypes that coincide with some observed collapsed vector $Z_i$. Collapsing loses information: the loss is small for rare variants and small pools, but for moderate or large pools, which save the most sequencing cost, the full pooled-data MLE computed by EM can be much more efficient.

## Sources

- Kuk AY, Li X, Xu J, Xu J. An EM algorithm based on an internal list for estimating haplotype distributions of rare variants from pooled genotype data. *BMC Genetics* 14:82 (2013), Methods, Eq. 1. <https://doi.org/10.1186/1471-2156-14-82>. PMCID: PMC3847674.
