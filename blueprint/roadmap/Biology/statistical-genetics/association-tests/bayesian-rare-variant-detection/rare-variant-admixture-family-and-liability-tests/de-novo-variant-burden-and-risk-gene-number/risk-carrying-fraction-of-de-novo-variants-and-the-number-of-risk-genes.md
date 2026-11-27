# Risk-carrying fraction of de novo variants and the number of risk genes

**Excess-rate model.** Let $M_1$ be the mean number of de novo damaging variants per case proband and $M_2$ the mean per control, measured in the same callable region. Assume each case variant is either a background variant, arising at the control rate, or a risk-carrying variant that contributes to the case's phenotype, and that controls carry only background variants. Then the expected fraction of case variants that carry risk is

$$E = \frac{M_1 - M_2}{M_1}.$$

For Tourette disorder (674 non-multiplex probands with 199 damaging de novo variants in consensus regions; 1,153 controls with 258),

$$E = \frac{199/674 - 258/1153}{199/674} \approx 0.242 .$$

**Recurrence estimator of the number of risk genes.** Suppose $G$ genes carry risk, chosen with probability proportional to their per-gene mutation probability (which accounts for gene size and sequence composition). Among $n$ observed case variants, a fraction $E$ is allocated to the risk genes and the remainder is treated as non-risk background variants. For each $G$ in a range, simulate this process many times and record how often the simulated recurrence pattern (the numbers of genes hit two, three, ... times) agrees with the observed one; the maximum-likelihood estimate $\hat G$ is the value maximizing this agreement frequency. With $n = 282$ confirmed variants, $6$ genes hit twice and $2$ genes hit three times, the estimate was $\hat G = 483$.

## Expansion

If case probands carry on average $M_2$ background variants plus $M_1 - M_2$ risk-carrying ones, the ratio of risk-carrying to all case variants is $(M_1 - M_2)/M_1$; the estimate is unbiased only under the stated mixture assumption and equal ascertainment of cases and controls, which is why both are restricted to the same consensus capture region. Recurrence is informative because background variants rarely hit the same gene twice, while risk-carrying variants concentrated on few genes produce many repeats: a small $G$ predicts more recurrent genes than observed, a very large $G$ predicts too few, and the Monte Carlo likelihood has an interior maximum.

## Sources

- S. Wang, J. D. Mandell, Y. Kumar, N. Sun, M. T. Morris, J. Arbelaez, C. Nasello, S. Dong, C. Duhn, X. Zhao, et al., *De novo sequence and copy number variants are strongly associated with Tourette disorder and implicate cell polarity in pathogenesis*, Cell Reports 24 (2018), <https://doi.org/10.1016/j.celrep.2018.08.082>, PMCID PMC6475626. STAR Methods, "Estimation of Total TD risk Genes by MLE" (formula and numerical value of $E$, permutation procedure over $1$ to $2500$ risk genes, observed recurrences, $\hat G = 483$); Results, "Approximately 483 Genes Contribute Risk to TD".
- J. Homsy, S. Zaidi, Y. Shen, et al., *De novo mutations in congenital heart disease with neurodevelopmental and other congenital anomalies*, Science 350 (2015), 1262–1266, <https://doi.org/10.1126/science.aac9396>.
