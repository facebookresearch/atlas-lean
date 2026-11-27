# Sensitivities of contingency-table association statistics

A randomized release of a statistic $f(D)$ of a genotype dataset $D$ is **$\epsilon$-differentially private** if neighbouring datasets (differing in one individual) produce output distributions whose densities differ by a factor at most $e^\epsilon$. With sensitivity $\Delta f = \max_{D \sim D'}|f(D) - f(D')|$, the **Laplace mechanism** releases $f(D) + b$ with $b \sim \mathrm{Laplace}(0, \Delta f/\epsilon)$ and is $\epsilon$-differentially private.

Consider a case–control GWAS with $N \ge 100$ individuals, $N/2$ cases and $N/2$ controls, all table margins positive; a $3\times 2$ table counts genotypes $0,1,2$ by status and a $2 \times 2$ table counts the $2N$ alleles. The sensitivities derived by Yamamoto and Shibuya (2021, Section 2) include the following; the last row replaces the source's value for the trend test, which is only a lower bound (see the Expansion):

| Statistic | Sensitivity | Large-$N$ value |
|---|---|---|
| $\log_{10}P$, $\chi^2$ test, $3\times 2$ | $\log_{10}(e)\cdot\dfrac{2N}{N+2}$ | $\approx 0.87$ |
| $\chi^2$ statistic, $2\times 2$ allelic | $\dfrac{8N}{N+2}$ | $\to 8$ |
| $\log_{10}P$, Fisher exact, $2\times 2$ | $\log_{10}\!\left(\tfrac12 (N+1)(N+2)\right)$ | $3.7, 5.7, 7.7$ at $N = 10^2, 10^3, 10^4$ |
| $\log_{10}P$, Fisher exact, $3\times 2$ | $\log_{10}\!\left(\tfrac N2 + 1\right)$ | $1.7, 2.7, 3.7$ at $N = 10^2, 10^3, 10^4$ |
| $\chi^2$, Cochran–Armitage trend | $\dfrac{16N(N^2+6N+4)}{(N^2+8N-4)(N+18)}$ | $\to 16$ |
| $\log_{10}P$, Cochran–Armitage trend | strictly more than $\tfrac12\log_{10}(e)\,\Delta_N$ and at most $-\log_{10}\Pr\bigl(\chi^2_1\ge\Delta_N\bigr)$, with $\Delta_N$ the trend $\chi^2$ sensitivity of the previous row | between $2.89$ and $3.58$ at $N=100$; bounds tend to $3.47$ and $4.20$ |

Releasing $\log_{10}P$ instead of $P$ is what makes the mechanism usable: the sensitivity of a raw P-value is of constant order, so Laplace noise swamps genome-wide thresholds near $10^{-8}$, whereas on the log scale a bounded noise scale can be compared with a threshold of about $8$.

## Depends on

- [Differential privacy](../../../../ComputerScience/cryptography/differential-privacy/differentially-private.md)
- [Laplace mechanism](../../../../ComputerScience/cryptography/laplace-and-exponential-mechanisms/laplace-mechanism.md)
- [Cochran–Armitage trend statistic](../../genomic-prediction-from-summary-statistics/trend-stat.md)
- [One-sided Fisher exact p-value](../../../../Probability/hypothesis-testing/fisher-s-exact-test/fisher-upper-pvalue.md)

## Expansion

The $\chi^2$ and trend statistics are smooth functions of four or six cell counts with fixed case/control margins; changing one individual moves one count between adjacent cells, and maximizing the change over admissible tables gives the rational expressions. For the two-degree-of-freedom $\chi^2$ test of the $3\times2$ table, $P=e^{-\chi^2/2}$ exactly, so its $\log_{10}P$ sensitivity is $\tfrac12\log_{10}e$ times the $\chi^2$ sensitivity. The trend test has one degree of freedom, and there this scaling fails. The $\chi^2_1$ hazard $h(x)=\phi(\sqrt x)/\bigl(2\sqrt x\,(1-\Phi(\sqrt x))\bigr)$ exceeds $\tfrac12$ everywhere and is decreasing, so for neighbouring tables with statistics $a<b$ the change $|\Delta\ln P|=\int_a^bh$ is strictly more than $(b-a)/2$ and at most $\int_0^{b-a}h=-\ln\Pr(\chi^2_1\ge b-a)$. Taking $b-a\le\Delta_N$ gives the upper bound in the table, and the pair attaining $\Delta_N$ gives the strict lower bound. At $N=100$ an exhaustive search over $3\times2$ tables gives $\Delta_N=13.318$ and a $\log_{10}P$ sensitivity of $2.924$, against $2.892$ for the half-scaled value the source states and $3.580$ for the upper bound. Laplace noise calibrated to the half-scaled value therefore does not give $\epsilon$-differential privacy; calibrating to the upper bound does. For Fisher's exact test, the P-value is a hypergeometric tail, and changing one individual changes it by at most a factor equal to the number of admissible tables, giving logarithmic sensitivities.

## Sources

- A. Yamamoto and T. Shibuya, *More practical differentially private publication of key statistics in GWAS*, Bioinformatics Advances 1(1) (2021), vbab004, Sections 2.1–2.3. <https://doi.org/10.1093/bioadv/vbab004> (PMCID: PMC9710635)
