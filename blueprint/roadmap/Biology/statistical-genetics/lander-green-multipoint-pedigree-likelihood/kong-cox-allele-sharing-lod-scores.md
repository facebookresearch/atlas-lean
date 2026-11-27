# Negative range of the Kong–Cox linear allele-sharing parameter

Kong and Cox (1997) start from an allele-sharing test statistic for linkage and propose an associated one-parameter model which, under general missing-data patterns, allows exact calculation of likelihood ratios and LOD scores; under the no-linkage hypothesis the parameter, written $\delta$, is $0$ (Margaritte-Jeannin et al. 2007). For the [linear model](../../not-yet-classified/kong-cox-allele-sharing/linear-model.md), [its total mass](../../not-yet-classified/kong-cox-allele-sharing/sum-linear-model.md), its [admissible range for $\delta \ge 0$](../../not-yet-classified/kong-cox-allele-sharing/linear-model-nonneg.md) and [the sharpness of that bound](../../not-yet-classified/kong-cox-allele-sharing/linear-model-neg-of-gt.md), and [the exact likelihood under missing data](../../not-yet-classified/kong-cox-allele-sharing/likelihood-eq.md), see those pages; this page states the range of negative $\delta$.

Let $Z$ be an allele-sharing score on the inheritance vectors $v$ of a pedigree, normalized to have mean $0$ and variance $1$ under the no-linkage law $P_0$ of $v$, and set $P_\delta(v) = P_0(v)(1 + \delta Z(v))$. For $\delta \le 0$, $P_\delta$ is a probability law (nonnegative with total mass $1$) if and only if $\delta \ge -1/\max Z$, the maximum taken over the support of $P_0$; for $\delta < -1/\max Z$ it is negative at every inheritance vector of the support where $Z$ attains its maximum.

## Depends on

- [Linear Model](../../not-yet-classified/kong-cox-allele-sharing/linear-model.md)
- [The linear model has total mass one](../../not-yet-classified/kong-cox-allele-sharing/sum-linear-model.md)
- [Inheritance Vector](inheritance-vector.md)

## Expansion

1. The model: inheritance vectors, the no-linkage law, and normalized sharing scores; $\max Z > 0$ on the support because $Z$ has mean $0$ and variance $1$.
2. Nonnegativity of $1 + \delta Z$ on the support for $-1/\max Z \le \delta \le 0$.
3. Negativity of $P_\delta$ at a maximizer of $Z$ for $\delta < -1/\max Z$.
4. The exponential family $P_\delta(v) \propto P_0(v) e^{\delta Z(v)}$, its normalizing constant, and its behaviour when the linear family's interval is too narrow, as a separate statement.
5. The relation of the score test at $\delta = 0$ to the normalized nonparametric linkage statistic, as a separate statement.

## Sources

- A. Kong and N. J. Cox, Allele-sharing models: LOD scores and accurate linkage tests, Am. J. Hum. Genet. 61 (1997), 1179–1188, abstract. <https://doi.org/10.1086/301592>
- P. Margaritte-Jeannin, M.-C. Babron and F. Clerget-Darpoux, On the choice of linkage statistics, BMC Proc. 1, Suppl. 1 (2007), S102, Methods. <https://doi.org/10.1186/1753-6561-1-s1-s102>
