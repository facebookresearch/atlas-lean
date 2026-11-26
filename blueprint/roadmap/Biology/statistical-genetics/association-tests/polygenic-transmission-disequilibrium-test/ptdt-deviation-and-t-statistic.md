# pTDT deviation and t statistic

Let $n$ families each consist of two genotyped parents and one child, with polygenic scores $S^{\mathrm c}_i$, $S^{\mathrm m}_i$, $S^{\mathrm f}_i$ for family $i = 1, \dots, n$ (computed with the same weights). Let $S_{\mathrm{MP},i} = (S^{\mathrm m}_i + S^{\mathrm f}_i)/2$ and let $\widehat{\mathrm{SD}}(S_{\mathrm{MP}})$ be the sample standard deviation of $S_{\mathrm{MP},1}, \dots, S_{\mathrm{MP},n}$. The **pTDT deviation** of family $i$ is

$$D_i = \frac{S^{\mathrm c}_i - S_{\mathrm{MP},i}}{\widehat{\mathrm{SD}}(S_{\mathrm{MP}})},$$

and the **pTDT statistic** is the one-sample $t$ statistic

$$t_{\mathrm{pTDT}} = \frac{\bar D}{\widehat{\mathrm{SD}}(D) / \sqrt{n}}, \qquad \bar D = \frac1n \sum_{i=1}^n D_i ,$$

referred to a two-sided $t$ distribution with $n - 1$ degrees of freedom (or a standard normal for large $n$).

**Null hypothesis and validity.** Suppose families are sampled independently and the children are not ascertained on any trait associated with the score (equivalently, transmissions follow Mendelian segregation conditionally on the parental genotypes and on the sampling event). Then by the [Mendelian expectation](mendelian-expectation-of-offspring-polygenic-score.md) each numerator $S^{\mathrm c}_i - S_{\mathrm{MP},i}$ has conditional mean $0$ given the parents, so $\bar D$ has mean $0$; the differences are independent across families, and with finite variance the central limit theorem gives $t_{\mathrm{pTDT}} \to N(0,1)$ in distribution as $n \to \infty$. Because the mean-zero property holds conditionally on every parental genotype configuration, the test is robust to population stratification. Under ascertainment of affected children, a positive $\bar D$ means that the score is over-transmitted, measured in standard deviations of the mid-parent distribution.

## Depends on

- [Mendelian expectation of an offspring polygenic score](mendelian-expectation-of-offspring-polygenic-score.md)

## Expansion

The common scale factor $\widehat{\mathrm{SD}}(S_{\mathrm{MP}})$ cancels in $t_{\mathrm{pTDT}}$, so it only makes $\bar D$ interpretable and comparable between different scores; the mid-parent distribution is used because it better proxies the population score distribution than the ascertained offspring. The paired design treats the untransmitted parental alleles as perfectly matched controls, which is why ancestry differences between families cannot create a nonzero mean. Unaffected siblings can replace parents, at a loss of power. Running the test on siblings without the phenotype provides a negative control: their deviations should average to zero.

## Sources

- D. J. Weiner, E. M. Wigdor, S. Ripke et al., "Polygenic transmission disequilibrium confirms that common and rare variation act additively to create risk for autism spectrum disorders", Nature Genetics 49 (2017), Online Methods "pTDT" (definitions of the pTDT deviation and $t_{\mathrm{pTDT}}$), <https://doi.org/10.1038/ng.3863>, PMCID PMC5552240.
