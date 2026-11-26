# Error rates for variant families of trait hypotheses

**Setting.** A multitrait association study tests $H_{it}$: no association between variant $i \in \{1, \dots, M\}$ and trait $t \in \{1, \dots, P\}$. The hypotheses are grouped into variant families $F_i = \{H_{it} : t = 1, \dots, P\}$ with global nulls $H_{i\bullet} = \bigcap_{t=1}^{P} H_{it}$ (variant $i$ affects no trait). A variant is discovered when $H_{i\bullet}$ is rejected. Let $R$ and $V$ be the numbers of all rejections and false rejections, $R_i$ and $V_i$ their counts within $F_i$, $R_v$ and $V_v$ the numbers of rejected and falsely rejected global nulls $H_{i\bullet}$, and $\mathcal S(\mathbf p)$ the data-dependent set of selected families.

**Definitions.**

$$\mathrm{gFDR} = \mathbb E\!\left[\frac{V}{\max\{R, 1\}}\right], \qquad \mathrm{aFDR} = \frac1M \sum_{i=1}^{M} \mathbb E\!\left[\frac{V_i}{\max\{R_i, 1\}}\right], \qquad \mathrm{vFDR} = \mathbb E\!\left[\frac{V_v}{\max\{R_v, 1\}}\right],$$

$$\mathrm{sFDR} = \mathbb E\!\left[\frac{1}{\max\{|\mathcal S(\mathbf p)|, 1\}} \sum_{i \in \mathcal S(\mathbf p)} \frac{V_i}{\max\{R_i, 1\}}\right],$$

together with $\mathrm{gFWER} = \Pr(V > 0)$ and $\mathrm{vFWER} = \Pr(V_v > 0)$.

**Non-equivalence.** These rates differ on the same rejections. In the five-family, eight-trait example of the source (Table 1), ten rejections include two true nulls, so the global false discovery proportion is $2/10$; three families are discovered and one of them contains only true nulls, so the variant-level proportion is $1/3$; the average within-family proportion is $(0 + 1 + 1/6 + 0 + 0)/5 = 0.2\overline{3}$ over all families but $(0 + 1 + 1/6)/3 = 0.3\overline{8}$ over the selected ones. So a bound on one of these rates does not by itself bound another. For instance, when the $MP$ P-values are independent and the true-null ones are valid, the [Benjamini–Hochberg (BH) procedure](../../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md) at level $q$ applied to the pooled $MP$ P-values has gFDR at most $q$, and applied separately in each family it has aFDR at most $q$, by [BH FDR control](../../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/integral-false-discovery-proportion-bh-r.md); neither bound extends to vFDR or sFDR, which in the source's simulations exceed $q$ under both strategies (Figure 1).

## Depends on

- [False discovery proportion](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/false-discovery-proportion.md)
- [Benjamini–Hochberg rejection set](../../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/bh-rejections.md)

## Proof depends on

- [Benjamini–Hochberg FDR control](../../../../Probability/hypothesis-testing/benjamini-hochberg-procedure/integral-false-discovery-proportion-bh-r.md)

## Expansion

Pooled BH spreads its false rejections uniformly over true nulls. When most variants affect no trait, these rejections land in otherwise null families, each of which then counts as a false variant discovery with within-family false discovery proportion $1$; the selected-family average is dominated by such families. Per-family BH ignores the multiplicity over $M$ variants: the many families with no rejections contribute $0$ to aFDR and hide large false discovery proportions in the families that are reported. In simulations with $M = 3000$ variants, $P = 100$ traits and $60$ variants each associated with $25$ traits, both strategies hit their own target while vFDR and sFDR exceed it (Figure 1 of the source).

The variant-family structure reflects how multitrait results are reported (lists of associated variants, each with the traits it influences); the grouping is a scientific choice, not a statement about dependence among the test statistics.

## Sources

- C. B. Peterson, M. Bogomolov, Y. Benjamini, C. Sabatti, "Many phenotypes without many false discoveries: error controlling strategies for multitrait association studies", Genetic Epidemiology 40 (2016) 45–56, section "Global Error Measures for Structured Hypotheses", Tables 1–2 and Figure 1, <https://doi.org/10.1002/gepi.21942>, PMCID PMC4738479.
