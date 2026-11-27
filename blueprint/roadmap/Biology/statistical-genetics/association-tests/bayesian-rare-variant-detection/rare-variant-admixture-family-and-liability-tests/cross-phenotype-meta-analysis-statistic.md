# Cross-phenotype meta-analysis (CPMA) statistic

Let one SNP have association $p$-values $p_1, \dots, p_n \in (0, 1]$ for $n$ phenotypes, assumed independent across phenotypes. Put $x_k = -\ln p_k$ and $S = \sum_{k=1}^{n} x_k$. Under the null hypothesis that the SNP has no association beyond those already known, the $p_k$ are i.i.d. uniform, so the $x_k$ are i.i.d. exponential with rate $\lambda = 1$. Model the $x_k$ as i.i.d. $\mathrm{Exp}(\lambda)$ with log-likelihood $\ell(\lambda) = n \ln \lambda - \lambda S$. The maximum-likelihood rate is $\hat\lambda = n / S$, and the **CPMA statistic** is the likelihood-ratio statistic for $H_0: \lambda = 1$,

$$\mathrm{CPMA} = 2\bigl[\ell(\hat\lambda) - \ell(1)\bigr] = 2\Bigl[n \ln \frac{n}{S} - n + S\Bigr].$$

**Proposition.** Under $H_0$, $\mathrm{CPMA} \to \chi^2_1$ in distribution as $n \to \infty$. A value of $\hat\lambda < 1$ (slower decay of $-\ln p$, i.e. an excess of small $p$-values) indicates association with several, though not necessarily all, of the phenotypes.

## Expansion

$\ell$ is strictly concave with $\ell'(\lambda) = n/\lambda - S$, so $\hat\lambda = n/S$, and substitution gives the closed form. Wilks' theorem for the one-parameter exponential family yields the $\chi^2_1$ limit; for finite $n$ the exact null law follows from $S \sim \mathrm{Gamma}(n, 1)$, since $\mathrm{CPMA}$ is a function of $S$ alone. Because a single rate parameter is tested, the statistic spends one degree of freedom however many phenotypes are combined, instead of testing every subset of phenotypes. As a two-sided test it also rejects for unusually large $p$-values ($\hat\lambda > 1$), which carries no evidence of sharing and is discarded in practice. Applied to 107 immune-mediated disease risk SNPs across seven diseases, 47 had $P_{\mathrm{CPMA}} < 0.01$, about one being expected by chance.

## Sources

- C. Cotsapas, B. F. Voight, E. Rossin, K. Lage, B. M. Neale, C. Wallace, G. R. Abecasis, J. C. Barrett, T. Behrens et al., "Pervasive sharing of genetic effects in autoimmune disease", PLoS Genetics (2011), e1002254, Results and Materials and Methods, "Cross-phenotype meta-analysis", <https://doi.org/10.1371/journal.pgen.1002254>, PMCID PMC3154137.
