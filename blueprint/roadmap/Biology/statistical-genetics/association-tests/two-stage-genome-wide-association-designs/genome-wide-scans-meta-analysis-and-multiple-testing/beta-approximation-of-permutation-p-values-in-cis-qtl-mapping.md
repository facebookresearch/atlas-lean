# Beta approximation of permutation p-values in cis-QTL mapping

Let a molecular phenotype $P$ be measured in $N$ samples and let $G$ hold genotype dosages at the $L$ variants in its cis window. For each variant compute the nominal p-value of the Pearson correlation with $P$ (equivalently, of $\beta \ne 0$ in $P = \beta g + \varepsilon$), and let $p_n$ be the smallest. To correct for the $L$ correlated tests, repeat the scan for $R$ random permutations of $P$, keeping $G$ fixed so that LD is preserved, and record the smallest nominal p-value $p_1, \dots, p_R$ of each permutation.

- **Direct permutation p-value.** If $r$ of the permutation minima are at least as extreme as the observed one, $p_d = (r + 1)/(R + 1)$, which can never fall below $1/(R+1)$.
- **Adaptive permutation p-value.** Permute until $B$ more extreme minima are seen or $M$ permutations are done; then $p_a = (\min(r, B) + 1)/(\min(R, M) + 1)$.
- **Beta approximation.** If the $L$ tests were independent, the minimum of $L$ independent $\mathrm{Uniform}(0,1)$ p-values would follow $\mathrm{Beta}(1, L)$, with $\Pr(U \le p) = 1 - (1 - p)^L$. LD makes the effective number of tests smaller than $L$, so FastQTL fits $U \sim \mathrm{Beta}(k, n)$ to the permutation minima by maximum likelihood,

$$\ell(k, n) = (k - 1)\sum_{r=1}^R \ln p_r + (n - 1)\sum_{r=1}^R \ln(1 - p_r) - R \ln B(k, n), \qquad B(k,n) = \frac{\Gamma(k)\Gamma(n)}{\Gamma(k+n)},$$

and reports the adjusted p-value $p_b = \Pr(U \le p_n)$ under the fitted law.

The fitted $n$ estimates the effective number of independent cis tests and $k$ stays near $1$, as expected for a minimum. Because $p_b$ uses the fitted tail rather than counting exceedances, it gives calibrated adjusted p-values far below $1/(R + 1)$ from a few hundred to a thousand permutations, and the per-phenotype values can then enter a genome-wide false discovery rate procedure such as Storey–Tibshirani across phenotypes.

## Remarks

For $U_1, \dots, U_L$ independent uniforms, $\Pr(\min_i U_i > p) = (1-p)^L$, so the minimum has density $L(1-p)^{L-1}$, the $\mathrm{Beta}(1, L)$ law; more generally the $j$-th order statistic of $L$ uniforms is $\mathrm{Beta}(j, L - j + 1)$. Treating $k$ and $n$ as free parameters lets the family absorb the dependence among tests caused by LD and the discreteness of genotypes. The log-likelihood is that of $R$ independent $\mathrm{Beta}(k, n)$ observations. In the Geuvadis European data the fitted $n$ was consistently smaller than the number of cis variants, a one-sample Kolmogorov–Smirnov test rejected the beta fit for only 2 of 13,703 genes, and the beta approximation with 500 permutations recovered the reference 5% FDR eQTL set as accurately as direct permutation with 1,000; the smallest adjusted p-value estimated was of order $10^{-128}$.

## Depends on

- [Monte Carlo permutation p-value](../../../../../Probability/hypothesis-testing/permutation-tests/monte-carlo-permutation-pvalue.md)

## Sources

- H. Ongen, A. Buil, A. A. Brown et al., "Fast and efficient QTL mapper for thousands of molecular phenotypes", Bioinformatics (2015), Sections 2.2–2.6 (Equations 1–5) and Section 3, <https://doi.org/10.1093/bioinformatics/btv722> (PMC4866519).
