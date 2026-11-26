# Upper bound on multiallelic $F_{ST}$ given the most frequent allele

Consider $K \ge 2$ equally weighted subpopulations and a locus with arbitrarily many alleles. Let $p_{k,i} \in [0,1]$ be the frequency of allele $i$ in subpopulation $k$, with $\sum_{i \ge 1} p_{k,i} = 1$ for every $k$. With $H_S$ and $H_T$ the mean within-subpopulation and total heterozygosities, $F_{ST} = (H_T - H_S)/H_T$, i.e.

$$F_{ST} = \frac{\frac{1}{K}\sum_{k=1}^{K}\sum_{i\ge 1} p_{k,i}^2 - \sum_{i \ge 1}\Big(\sum_{k=1}^{K} \frac{p_{k,i}}{K}\Big)^2}{1 - \sum_{i\ge 1}\Big(\sum_{k=1}^{K} \frac{p_{k,i}}{K}\Big)^2}.$$

Label alleles so that allele 1 has the largest pooled frequency $M = \frac{1}{K}\sum_k p_{k,1}$, and write $\sigma_1 = KM \in (0,K)$.

**Lower bound.** $F_{ST} \ge 0$ for every $M$, with equality exactly when all $K$ subpopulations have identical allele-frequency vectors.

**Upper bound.** With $J = \lceil 1/\sigma_1 \rceil$, $\lfloor x \rfloor$ and $\{x\} = x - \lfloor x \rfloor$ the integer and fractional parts,

$$F_{ST} \le \begin{cases} 1, & \sigma_1 \in \{1,2,\dots,K-1\},\\[4pt] \dfrac{(K-1)\,\big[1 - \sigma_1 (J-1)(2 - J\sigma_1)\big]}{K - \big[1 - \sigma_1 (J-1)(2 - J\sigma_1)\big]}, & 0 < \sigma_1 < 1,\\[10pt] \dfrac{K(K-1) - \sigma_1^2 + \lfloor\sigma_1\rfloor - 2(K-1)\{\sigma_1\} + (2K-1)\{\sigma_1\}^2}{K(K-1) - \sigma_1^2 - \lfloor\sigma_1\rfloor + 2\sigma_1 - \{\sigma_1\}^2}, & 1 < \sigma_1 < K,\ \sigma_1 \notin \mathbb{Z}. \end{cases}$$

The bound is continuous in $\sigma_1$ and equals 1 exactly at the integers $\sigma_1 = 1,\dots,K-1$.

**Equality at integer $\sigma_1$.** $F_{ST} = 1$ if and only if allele 1 has frequency 1 in exactly $\sigma_1$ subpopulations and each of the other $K - \sigma_1$ subpopulations is fixed for some allele other than allele 1.

## Depends on

- [Wright's hierarchical F-statistics identity](../hierarchical-f-statistics.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Since $H_T$ and $H_S$ share the cross term $2\sum_{i\ge 2}\sum_{k<\ell} p_{k,i}p_{\ell,i}$, which is subtracted from both numerator and denominator, $F_{ST}$ is largest when alleles $i \ge 2$ each occur in at most one subpopulation; the problem then reduces to maximizing the sum of squared frequencies $S = \sum_{i,k} p_{k,i}^2$ subject to the row sums being 1 and the column sums of alleles $i \ge 2$ not exceeding $\sigma_1$. For $\sigma_1 < 1$, allele 1 sits in one subpopulation and every subpopulation is filled greedily with alleles of pooled count $\sigma_1$, giving $S \le K[1 - \sigma_1(J-1)(2 - J\sigma_1)]$. For non-integer $\sigma_1 > 1$, the allele-1 mass is concentrated as $\lfloor\sigma_1\rfloor$ ones plus one fractional entry $\{\sigma_1\}$, and the rest of that row is completed by private alleles. Setting $K = 2$ recovers the two-population multiallelic bound of Jakobsson, Edge and Rosenberg, and restricting to two alleles recovers the biallelic $K$-population bound.

## Sources

- N. Alcala, N. A. Rosenberg, "Mathematical constraints on $F_{ST}$: multiallelic markers in arbitrarily many populations", Philosophical Transactions of the Royal Society B 377 (2022) 20200414, Section 2 (Eq. 2.1), Section 3 (Eq. 3.1) and Appendix A (Theorems A.1–A.2), <https://doi.org/10.1098/rstb.2020.0414>, PMCID PMC9014193.
