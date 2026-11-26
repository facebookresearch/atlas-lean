# Sensitivities of contingency-table association statistics

A randomized release of a statistic $f(D)$ of a genotype dataset $D$ is **$\epsilon$-differentially private** if neighbouring datasets (differing in one individual) produce output distributions whose densities differ by a factor at most $e^\epsilon$. With sensitivity $\Delta f = \max_{D \sim D'}|f(D) - f(D')|$, the **Laplace mechanism** releases $f(D) + b$ with $b \sim \mathrm{Laplace}(0, \Delta f/\epsilon)$ and is $\epsilon$-differentially private.

Consider a case–control GWAS with $N \ge 100$ individuals, $N/2$ cases and $N/2$ controls, all table margins positive; a $3\times 2$ table counts genotypes $0,1,2$ by status and a $2 \times 2$ table counts the $2N$ alleles. The sensitivities derived by Yamamoto and Shibuya (2021, Section 2) include:

| Statistic | Sensitivity | Large-$N$ value |
|---|---|---|
| $\log_{10}P$, $\chi^2$ test, $3\times 2$ | $\log_{10}(e)\cdot\dfrac{2N}{N+2}$ | $\approx 0.87$ |
| $\chi^2$ statistic, $2\times 2$ allelic | $\dfrac{8N}{N+2}$ | $\to 8$ |
| $\log_{10}P$, Fisher exact, $2\times 2$ | $\log_{10}\!\left(\tfrac12 (N+1)(N+2)\right)$ | $3.7, 5.7, 7.7$ at $N = 10^2, 10^3, 10^4$ |
| $\log_{10}P$, Fisher exact, $3\times 2$ | $\log_{10}\!\left(\tfrac N2 + 1\right)$ | $1.7, 2.7, 3.7$ at $N = 10^2, 10^3, 10^4$ |
| $\chi^2$, Cochran–Armitage trend | $\dfrac{16N(N^2+6N+4)}{(N^2+8N-4)(N+18)}$ | $\to 16$ |
| $\log_{10}P$, Cochran–Armitage trend | $\log_{10}(e)\cdot\dfrac{8N(N^2+6N+4)}{(N^2+8N-4)(N+18)}$ | $\approx 3.47$ |

Releasing $\log_{10}P$ instead of $P$ is what makes the mechanism usable: the sensitivity of a raw P-value is of constant order, so Laplace noise swamps genome-wide thresholds near $10^{-8}$, whereas on the log scale a bounded noise scale can be compared with a threshold of about $8$.

## Depends on

- [Differential privacy](../../../../ComputerScience/cryptography/differential-privacy/differentially-private.md)
- [Laplace mechanism](../../../../ComputerScience/cryptography/laplace-and-exponential-mechanisms/laplace-mechanism.md)
- [Cochran–Armitage trend statistic](../../genomic-prediction-from-summary-statistics/trend-stat.md)
- [One-sided Fisher exact p-value](../../../../Probability/hypothesis-testing/fisher-s-exact-test/fisher-upper-pvalue.md)

## Expansion

The $\chi^2$ and trend statistics are smooth functions of four or six cell counts with fixed case/control margins; changing one individual moves one count between adjacent cells, and maximizing the change over admissible tables gives the rational expressions. For one-degree-of-freedom tests, $-\ln P$ grows asymptotically like $\chi^2/2$, which is why each $\log_{10}P$ sensitivity is about $\tfrac12\log_{10}e$ times the corresponding $\chi^2$ sensitivity. For Fisher's exact test, the P-value is a hypergeometric tail, and changing one individual changes it by at most a factor equal to the number of admissible tables, giving logarithmic sensitivities.

## Sources

- A. Yamamoto and T. Shibuya, *More practical differentially private publication of key statistics in GWAS*, Bioinformatics Advances 1(1) (2021), vbab004, Sections 2.1–2.3. <https://doi.org/10.1093/bioadv/vbab004> (PMCID: PMC9710635)
