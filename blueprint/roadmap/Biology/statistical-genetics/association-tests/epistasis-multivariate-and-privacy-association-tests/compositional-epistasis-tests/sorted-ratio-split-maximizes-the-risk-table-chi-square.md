# Sorted-ratio split maximizes the risk-table chi-square

Let a categorical variable with categories $1,\dots,M$ (for two SNPs, the $M = 9$ joint genotypes) be observed in two classes with counts $s_i$ (class $Y=0$) and $t_i$ (class $Y=1$), $s_i + t_i > 0$, and order the categories so that the ratios $r_i = s_i/(s_i+t_i)$ satisfy $r_1 \le r_2 \le \cdots \le r_M$. For a bipartition of the categories into nonempty groups $L$ and $R$, let $X^2(L,R)$ be the Pearson chi-square statistic of the $2\times 2$ table of group by class. Then the maximum of $X^2(L,R)$ over all $2^{M-1}-1$ bipartitions is attained at one of the $M-1$ contiguous splits $L = \{1,\dots,m\}$, $R = \{m+1,\dots,M\}$, $1 \le m < M$. The same contiguous splits contain a bipartition that minimizes the misclassification rate of the rule that predicts the majority class in each group.

Hence the largest [risk-table chi-square](binary-penetrance-models-and-the-risk-table-chi-square-test.md) over all 512 binary penetrance models of a SNP pair is found by checking 8 splits. In a genome-wide scan this maximum is a cheap upper bound: pairs whose maximum stays below a threshold are discarded, and only the survivors are tested against every non-redundant model with a Bonferroni correction.

## Depends on

- [Binary penetrance models and the risk-table chi-square test](binary-penetrance-models-and-the-risk-table-chi-square-test.md)
- [Pearson's chi-squared statistic of a 2 × 2 table](../../../genomic-prediction-from-summary-statistics/pearson2x2.md)

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Expansion

For two classes, $X^2(L,R) = \sum_{G\in\{L,R\}} n_G(\hat r_G - \hat r)^2\big/\bigl(\hat r(1-\hat r)\bigr)$, where $n_G$ is the size of group $G$, $\hat r_G$ its class-$0$ proportion and $\hat r$ the overall one, so $X^2$ is a fixed multiple of the reduction in Gini impurity. Writing $S_G$ for the class-$0$ count of $G$, the numerator is $\sum_G S_G^2/n_G - n\hat r^2$, a convex function of the totals $(S_L, n_L)$ of $L$, so its maximum over the polytope of fractional assignments of categories to $L$ is at a vertex, and an exchange argument shows that any vertex that is not contiguous in the ratio order can be moved to a contiguous one without decreasing the criterion. This is the theorem of Breiman, Friedman, Olshen and Stone (1984) on optimal splits of categorical predictors for two classes; it fails for more than two classes.

## Sources

- X. Wan, C. Yang, Q. Yang, H. Zhao and W. Yu, "The complete compositional epistasis detection in genome-wide association studies", BMC Genetics 14 (2013), 7, <https://doi.org/10.1186/1471-2156-14-7>, PMCID PMC3638013. Theorem 1 and Table 5; the theorem is from L. Breiman, J. Friedman, R. Olshen and C. Stone, *Classification and Regression Trees* (1984).
