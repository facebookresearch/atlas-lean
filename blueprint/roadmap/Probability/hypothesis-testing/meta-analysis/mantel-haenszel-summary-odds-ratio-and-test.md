# Mantel–Haenszel summary odds ratio and test

For subclassifications $i = 1, \dots, K$ with $2 \times 2$ tables $(A_i, B_i; C_i, D_i)$ (diseased with and without the factor; disease-free with and without the factor), row totals $N_{1i}, N_{2i}$, column totals $M_{1i}, M_{2i}$ and total $T_i \ge 2$ (strata with $T_i < 2$ are dropped), Mantel and Haenszel (1959) compare $A_i$ with its expectation, given the margins, under the null hypothesis of no association between factor and disease in any subclassification (odds ratio $1$ in every table), $E(A_i) = N_{1i} M_{1i}/T_i$, with variance subject to the fixed margins $V(A_i) = N_{1i} N_{2i} M_{1i} M_{2i}/(T_i^2 (T_i - 1))$; these are the hypergeometric [mean](../../distributions/discrete/hypergeometric-distribution/sum-mul-hypergeometric-real.md) $nS/N$ and [variance](../../distributions/discrete/hypergeometric-distribution/sum-sq-sub-mean-mul-hypergeometric-real.md) $nS(N - S)(N - n)/(N^2(N - 1))$ of the number of successes in $n$ draws without replacement from $N$ items of which $S$ are successes, with $N = T_i$, $S = M_{1i}$ and $n = N_{1i}$, since $A_i$ given the margins is the number of factor-positive individuals among the $N_{1i}$ diseased drawn without replacement from the $T_i$. The tables are conditionally independent across strata given their margins, as when the strata are sampled independently, so under the null hypothesis $\sum_i A_i - \sum_i E(A_i)$ has exact conditional mean $0$ and exact conditional variance $\sum_i V(A_i)$. Assume $\sum_i V(A_i) > 0$ and $\sum_i B_i C_i / T_i > 0$, so that the denominators below are positive. The overall test statistic, with power against an association in the same direction across subclassifications, is the corrected chi square

$$\frac{\bigl(\lvert \sum_i A_i - \sum_i E(A_i) \rvert - \tfrac12\bigr)^2}{\sum_i V(A_i)},$$

referred to the $\chi^2$ distribution with one degree of freedom as a large-sample approximation, and the summary odds ratio is

$$R = \frac{\sum_i A_i D_i / T_i}{\sum_i B_i C_i / T_i}.$$

Since $A_i - E(A_i) = (A_i D_i - B_i C_i)/T_i$, $R = 1$ exactly when $\sum_i A_i = \sum_i E(A_i)$, so the chi-square test is a test of the departure of $R$ from $1$; and if every subclassification has the same cross-product ratio, $R$ equals it. Mantel and Haenszel use $R$ to estimate the relative risk of a rare disease from a retrospective study.

## Depends on

- [Hypergeometric distribution](../../distributions/discrete/hypergeometric-distribution/hypergeometric.md)
- [Mean of the hypergeometric distribution](../../distributions/discrete/hypergeometric-distribution/sum-mul-hypergeometric-real.md)
- [Variance of the hypergeometric distribution](../../distributions/discrete/hypergeometric-distribution/sum-sq-sub-mean-mul-hypergeometric-real.md)

## Expansion

1. The model: stratified $2 \times 2$ tables, the conditional null hypothesis of no association within strata, and the common-odds-ratio alternative.
2. The conditional hypergeometric law of $A_i$ given the margins under the null hypothesis.
3. The exact conditional mean and variance of $\sum_i A_i$ under conditional independence across strata, and, as a separate statement, the large-sample $\chi^2_1$ limit of the summary statistic, with conditions on the strata.
4. The identity $A_i - E(A_i) = (A_i D_i - B_i C_i)/T_i$ and the relation between the test and $R$.
5. Consistency of $R$ for a common odds ratio, both as the number of strata grows with bounded sizes and as the stratum sizes grow with $K$ fixed, from $E[A_i D_i - \psi B_i C_i \mid \text{margins}] = 0$, as separate statements.

## Sources

- N. Mantel and W. Haenszel, Statistical aspects of the analysis of data from retrospective studies of disease, J. Natl. Cancer Inst. 22 (1959), 719–748, sections on the analysis of subclassified data and on the summary estimate. <https://doi.org/10.1093/jnci/22.4.719>
