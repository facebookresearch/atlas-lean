# Brown's method for combining dependent p-values

Let $p_1, \dots, p_k$ be one-sided p-values for the same gene from $k$ data sources, each $\mathrm{Uniform}(0,1)$ under the null but possibly dependent. Fisher's statistic is

$$X = -2\sum_{i=1}^{k}\log p_i .$$

Under independence $X \sim \chi^2_{2k}$. In general

$$\mathbb E X = 2k, \qquad \operatorname{Var} X = 4k + 2\sum_{i<j}\operatorname{Cov}\bigl(-2\log p_i,\,-2\log p_j\bigr).$$

Brown's method approximates the null law of $X$ by a scaled chi-square $c\,\chi^2_f$ with the same first two moments:

$$c = \frac{\operatorname{Var} X}{2\,\mathbb E X}, \qquad f = \frac{2\,(\mathbb E X)^2}{\operatorname{Var} X}, \qquad p_{\mathrm{Brown}} = \Pr\bigl(\chi^2_f > X/c\bigr).$$

The covariances are estimated from the empirical covariation of the p-values across all genes. With independent sources $c = 1$ and $f = 2k$, recovering Fisher's test; positive dependence gives $c > 1$ and $f < 2k$, producing a more dispersed null distribution with the same mean $2k$, so in the upper tail (large $X$, i.e. small Fisher p-values) the same $X$ receives a larger, more conservative p-value.

## Expansion

If $p \sim \mathrm{Uniform}(0,1)$ then $-2\log p \sim \chi^2_2$, with mean $2$ and variance $4$, which gives $\mathbb E X$ and the diagonal part of $\operatorname{Var} X$. A $c\chi^2_f$ variable has mean $cf$ and variance $2c^2 f$; equating these with $\mathbb E X$ and $\operatorname{Var} X$ gives $c$ and $f$. Without the correction, correlated omics signals (for example mRNA abundance and copy number of the same gene) would be counted as independent confirmations and the combined p-values would be anti-conservative. In the integrative pathway method, genes are ranked by $p_{\mathrm{Brown}}$ and filtered at a lenient threshold (unadjusted $p < 0.1$) before enrichment testing.

## Sources

- M. Paczkowska, J. Barenboim, N. Sintupisut, et al., "Integrative pathway enrichment analysis of multivariate omics data", Nature Communications 11 (2020), Methods ("ActivePathways"), <https://doi.org/10.1038/s41467-019-13983-9> (PMC7002665).
- M. B. Brown, "A method for combining non-independent, one-sided tests of significance", Biometrics 31 (1975) 987–992, <https://doi.org/10.2307/2529826>.
