# Effective-sample-size adjusted correlation test for regulatory edges

Let $X$ be a doubly standardized $p \times n$ expression compendium with gene-gene correlations $\hat\Sigma_{ii'}$ and [effective number of experiments](effective-numbers-of-genes-and-experiments-coincide.md) $n_{\mathrm{eff}} > 3$. The **$n_{\mathrm{eff}}$-adjusted relevance network** for transcriptional regulatory network inference is:

1. compute the Fisher transforms $z_{ii'} = \frac12 \log \frac{1 + \hat\Sigma_{ii'}}{1 - \hat\Sigma_{ii'}}$;
2. compute two-sided p-values for each transcription factor-gene pair against the null distribution
$$z_{ii'} \sim N\big(0, (n_{\mathrm{eff}} - 3)^{-1}\big);$$
3. order the $m$ p-values $p_{(1)} \le \dots \le p_{(m)}$ and report as edges the pairs with $p_{(k)} \le q k / m$ (Benjamini-Hochberg control of the false discovery rate at level $q$).

(Eqs. (7)-(10) of the source.) With independent experiments the classical null is $N(0, (n-3)^{-1})$; replacing $n$ by $n_{\mathrm{eff}}$ widens the null to account for dependence between microarrays.

## Expansion

For independent bivariate normal samples Fisher's transform is variance-stabilizing, with variance approximately $(n - 3)^{-1}$ whatever the true correlation. When experiments are dependent the variance of sample correlations scales like $n_{\mathrm{eff}}^{-1}$ rather than $n^{-1}$, and the source substitutes $n_{\mathrm{eff}}$ in the nominal formula in the spirit of empirical-null modeling. On the *E. coli* compendium, the nominal false discovery rate obtained this way closely matched the empirical false discovery rate measured against a curated database of known regulatory interactions.

## Depends on

- [Effective numbers of genes and of experiments coincide](effective-numbers-of-genes-and-experiments-coincide.md)

## Sources

- E. J. Cosgrove, T. S. Gardner and E. D. Kolaczyk, *On the choice and number of microarrays for transcriptional regulatory network inference*, BMC Bioinformatics 11 (2010), 454. DOI: <https://doi.org/10.1186/1471-2105-11-454>. PMCID: PMC2949888.
- B. Efron, *Are a set of microarrays independent of each other?*, Annals of Applied Statistics 3(3) (2009), 922-942. DOI: <https://doi.org/10.1214/09-AOAS236>.
