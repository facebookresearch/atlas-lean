# Effective numbers of genes and of experiments coincide

Let $X$ be a $p \times n$ gene-by-experiment expression matrix that is **doubly standardized**: every row and every column has mean $0$ and variance $1$ (with divisors $n$ and $p$ respectively). The sample gene-gene and experiment-experiment correlation matrices are

$$\hat\Sigma = \frac{1}{n} X X^\top, \qquad \hat\Delta = \frac{1}{p} X^\top X,$$

both with unit diagonal. Let $\hat\alpha^2$ be the mean of the squared off-diagonal entries of $\hat\Sigma$ and $\hat c^2$ that of $\hat\Delta$, and define the **effective number of genes** and the **effective number of experiments**

$$\hat p_{\mathrm{eff}} = \frac{p}{1 + (p - 1)\hat\alpha^2}, \qquad \hat n_{\mathrm{eff}} = \frac{n}{1 + (n - 1)\hat c^2}.$$

**Proposition (Eq. (6) of the source, from Theorem 1 of Efron 2009).**

$$\hat\alpha^2 = \frac{p \big[ 1 + \hat c^2 (n - 1) \big] - n}{n (p - 1)}, \qquad \text{hence} \qquad \hat p_{\mathrm{eff}} = \hat n_{\mathrm{eff}}.$$

Under the matrix-normal model $X \sim N_{p,n}(0, \Sigma \otimes \Delta)$, the population versions satisfy $\operatorname{Var}(\hat\Delta_{jj'}) \propto p_{\mathrm{eff}}^{-1}$ and, by the symmetric argument, $\operatorname{Var}(\hat\Sigma_{ii'}) \propto n_{\mathrm{eff}}^{-1}$, so $n_{\mathrm{eff}}$ plays the role of the sample size for gene-gene correlations in place of the nominal number of experiments $n$.

## Expansion

The identity follows from $\operatorname{tr}\big((XX^\top)^2\big) = \operatorname{tr}\big((X^\top X)^2\big)$, that is $n^2 \|\hat\Sigma\|_F^2 = p^2 \|\hat\Delta\|_F^2$. With unit diagonals, $\|\hat\Sigma\|_F^2 = p + p(p-1)\hat\alpha^2$ and $\|\hat\Delta\|_F^2 = n + n(n-1)\hat c^2$; solving for $\hat\alpha^2$ gives the formula, and substituting it gives $1 + (p-1)\hat\alpha^2 = p\big(1 + (n-1)\hat c^2\big)/n$, so $\hat p_{\mathrm{eff}} = \hat n_{\mathrm{eff}}$. Dependence between experiments, from shared laboratory protocols and from gene-gene correlation itself, can shrink the effective sample size dramatically: for an *Escherichia coli* compendium of $n = 376$ experiments the source finds $n_{\mathrm{eff}} \approx 14.7$, and well-chosen subsets of experiments can have a larger $n_{\mathrm{eff}}$ than the full compendium.

## Sources

- E. J. Cosgrove, T. S. Gardner and E. D. Kolaczyk, *On the choice and number of microarrays for transcriptional regulatory network inference*, BMC Bioinformatics 11 (2010), 454. DOI: <https://doi.org/10.1186/1471-2105-11-454>. PMCID: PMC2949888.
- B. Efron, *Are a set of microarrays independent of each other?*, Annals of Applied Statistics 3(3) (2009), 922-942. DOI: <https://doi.org/10.1214/09-AOAS236>.
