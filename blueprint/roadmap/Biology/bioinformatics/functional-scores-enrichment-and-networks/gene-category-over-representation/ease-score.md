# EASE score

In the setting of the [hypergeometric over-representation test](hypergeometric-over-representation-test.md), with population size $N$, category size $M$, list size $n \ge 1$ and $k \ge 1$ category genes on the list, the **EASE score** is the one-tailed Fisher exact probability recomputed after removing one category gene from the list:

$$p_{\mathrm{EASE}}(k; N, M, n) = p_{\mathrm F}(k-1; N, M, n-1) = \Pr(X' \ge k-1), \qquad X' \sim \mathrm{Hypergeometric}(N, M, n-1).$$

**Proposition.**

1. $p_{\mathrm{EASE}}(k; N,M,n) \ge p_{\mathrm F}(k; N,M,n)$.
2. $p_{\mathrm{EASE}}(1; N,M,n) = 1$: a category supported by a single list gene is never significant.
3. Among the $k$ jackknife probabilities obtained by deleting one category gene from the list, all are equal to $p_{\mathrm{EASE}}$, and deleting a non-category gene instead gives $p_{\mathrm F}(k; N,M,n-1) \le p_{\mathrm{EASE}}$; hence $p_{\mathrm{EASE}}$ is the largest delete-one jackknife value of the Fisher probability.

## Depends on

- [Hypergeometric over-representation test](hypergeometric-over-representation-test.md)

## Remarks

Couple the two hypergeometric laws by drawing genes one at a time without replacement: $X_n$ is the category count after $n$ draws and $X_{n-1}$ after $n-1$. Since one draw changes the count by at most one, $X_n \ge k$ implies $X_{n-1} \ge k-1$, which gives (1). Part (2) holds because $X' \ge 0$ always. For (3), deleting any category gene yields counts $(k-1, n-1)$, and deleting a non-category gene yields $(k, n-1)$, whose tail is smaller. The effect is a penalty that is severe for categories with few list genes and mild for well-supported ones. In the source's example (a 206-gene list from 13,679 genes), a category with one population member that lands on the list has Fisher probability about $0.015$ but EASE score $1$, whereas a category with 787 members and 20 list genes has Fisher probability about $0.015$ and EASE score about $0.027$, consistent with the reported $p < 0.0274$.

## Sources

- D. A. Hosack, G. Dennis Jr, B. T. Sherman, H. C. Lane and R. A. Lempicki, "Identifying biological themes within lists of genes with EASE", Genome Biology 4 (2003) R70, Results (EASE score as a jackknifed Fisher exact probability; worked example of categories X and Y), <https://doi.org/10.1186/gb-2003-4-10-r70>, PMCID PMC328459.
