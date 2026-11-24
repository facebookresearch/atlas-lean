# Sib transmission/disequilibrium test

Spielman and Ewens (1998) introduce the sib transmission/disequilibrium test (S-TDT), which applies the principle of the transmission/disequilibrium test to sibships without parental data by comparing the marker genotypes of affected sibs with those of their unaffected sibs, and show how TDT families and S-TDT sibships can be combined in one overall test of linkage in the presence of association. The conditional null distribution on which it rests is the following exchangeability statement. Fix a marker allele $M$ and, in a sibship with $a$ affected and $u$ unaffected sibs, condition on the multiset of the sibs' marker genotypes. If, under the null hypothesis, every assignment of these genotypes to the sibs is equally likely given the affection statuses, then the number $Y$ of copies of $M$ carried by the affected sibs is the total of a sample of size $a$ drawn without replacement from the $t = a + u$ copy numbers $c_1, \dots, c_t \in \{0, 1, 2\}$, so

$$E[Y] = a \bar c, \qquad \operatorname{Var}(Y) = \frac{a u}{t (t - 1)} \sum_{j=1}^t (c_j - \bar c)^2, \qquad \bar c = \frac1t \sum_j c_j .$$

Summing $Y - E[Y]$ and the variances over independent sibships gives a standardized statistic whose conditional null law does not depend on the population allele frequencies, because each sibship is compared only with itself.

## Depends on

- [Hypergeometric distribution](../../../Probability/distributions/discrete/hypergeometric-distribution/hypergeometric.md)

## Expansion

1. The model: sibships, marker genotypes, affection status, and the null hypothesis as within-sibship exchangeability of genotypes with respect to affection.
2. The conditional mean and variance of $Y$ from the moments of sampling without replacement.
3. The standardized statistic and its asymptotic normality as the number of independent sibships grows.
4. Robustness to population stratification, and the combination with the parental transmission/disequilibrium test (whose [one-sided exact test is valid](../../../Biology/statistical-genetics/transmission-disequilibrium-test/is-valid-pvalue-tdt-pvalue.md)), as separate statements.

## Sources

- R. S. Spielman and W. J. Ewens, A sibship test for linkage in the presence of association: the sib transmission/disequilibrium test, Am. J. Hum. Genet. 62 (1998), 450–458, abstract. <https://doi.org/10.1086/301714>
