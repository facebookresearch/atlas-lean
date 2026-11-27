# Standardized sib transmission/disequilibrium statistic

Spielman and Ewens (1998) introduce the sib transmission/disequilibrium test (S-TDT), which applies the principle of the transmission/disequilibrium test to sibships without parental data by comparing the marker genotypes of affected sibs with those of their unaffected sibs, and show how TDT families and S-TDT sibships can be combined in one overall test of linkage in the presence of association. Fix a marker allele $M$ and, in a sibship with $a \ge 1$ affected and $u \ge 1$ unaffected sibs, condition on the multiset of the sibs' marker genotypes, with copy numbers $c_1, \dots, c_t \in \{0, 1, 2\}$ of $M$, $t = a + u$. Under the null hypothesis every assignment of these genotypes to the sibs is equally likely given the affection statuses, so the set of affected sibs is uniformly distributed over the $a$-element subsets of the sibship, and the number $Y$ of copies of $M$ carried by the affected sibs has the conditional [null mean](../../not-yet-classified/sib-transmission-disequilibrium/rand-exp-affected-allele-count.md) $E[Y]$ and [null variance](../../not-yet-classified/sib-transmission-disequilibrium/rand-exp-sq-sub-mean.md) $\operatorname{Var}(Y)$ of the S-TDT count.

This page states the statistic built from these moments. A sibship whose sibs all carry the same number of copies has $\operatorname{Var}(Y) = 0$ and contributes nothing. Summing $Y - E[Y]$ and the variances over independent sibships gives a standardized statistic, defined when the total conditional variance is positive, whose conditional null law does not depend on the population allele frequencies, because each sibship is compared only with itself. Its normal limit needs a condition that ensures a central limit theorem, for example bounded sibship sizes together with a total conditional variance tending to infinity: adding any number of zero-variance sibships to one informative sibship leaves the statistic's discrete law unchanged.

## Depends on

- [Null mean of the S-TDT count](../../not-yet-classified/sib-transmission-disequilibrium/rand-exp-affected-allele-count.md)
- [Null variance of the S-TDT count](../../not-yet-classified/sib-transmission-disequilibrium/rand-exp-sq-sub-mean.md)

## Expansion

1. The model: sibships, marker genotypes, affection status, and the null hypothesis as within-sibship exchangeability of genotypes with respect to affection.
2. The standardized statistic, for positive total conditional variance, and its asymptotic normality under bounded sibship sizes and diverging total conditional variance.
3. Robustness to population stratification, and the combination with the parental transmission/disequilibrium test (whose [one-sided exact test is valid](../../../Biology/statistical-genetics/transmission-disequilibrium-test/is-valid-pvalue-tdt-pvalue.md)), as separate statements.

## Sources

- R. S. Spielman and W. J. Ewens, A sibship test for linkage in the presence of association: the sib transmission/disequilibrium test, Am. J. Hum. Genet. 62 (1998), 450–458, abstract. <https://doi.org/10.1086/301714>
