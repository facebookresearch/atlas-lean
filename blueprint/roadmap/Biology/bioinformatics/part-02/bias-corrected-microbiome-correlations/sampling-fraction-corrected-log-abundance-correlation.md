# Sampling-fraction-corrected log-abundance correlation

**Model.** For samples $i = 1, \dots, n$ and taxa $j = 1, \dots, d$, let $A_{ij} \ge 0$ be the unobserved absolute abundance and $O_{ij}$ the observed count. Presence indicators $M_{ij} \in \{0,1\}$ are random with $M_i = (M_{i1}, \dots, M_{id})$ independent across samples. When $M_{ij} = 1$,

$$O_{ij} = S_i\, C_j\, A_{ij}\, E_{ij}, \qquad o_{ij} = s_i + c_j + a_{ij} + e_{ij}$$

(lower case denotes logarithms), where $s_i$ is a sample-specific sampling fraction, $c_j$ a taxon-specific sequencing efficiency, $\mathbb{E}(a_{ij}) = \alpha_j$, $\operatorname{Cov}(a_{il}, a_{im}) = \sigma^0_{lm}$, and $e_{ij}$ i.i.d. with mean $0$ and variance $\sigma_e^2$. The target is the correlation matrix $R^0 = [\rho^0_{lm}]$ of the log absolute abundances.

**Bias removal.** Centering over samples eliminates $c_j$:

$$o_{ij} - \bar o_{\cdot j} = (s_i - \bar s_{\cdot}) + (a_{ij} - \bar a_{\cdot j}) + (e_{ij} - \bar e_{\cdot j}).$$

With $d(i) = \{ j : M_{ij} = 1 \}$, the sampling-fraction difference is estimated by a (variance-weighted) average over the taxa present in sample $i$,

$$\widehat{s_i - \bar s_{\cdot}} = \sum_{j \in d(i)} w_j\, (o_{ij} - \bar o_{\cdot j}), \qquad w_j \propto \frac{1}{\operatorname{Var}(o_{ij} - \bar o_{\cdot j})}, \ \ \sum_{j\in d(i)} w_j = 1,$$

and $\hat y_{ij} = (o_{ij} - \bar o_{\cdot j}) - \widehat{s_i - \bar s_{\cdot}}$ converges in probability to $y_{ij} = (a_{ij} - \bar a_{\cdot j}) + (e_{ij} - \bar e_{\cdot j})$ as $|d(i)| \to \infty$, provided the covariance matrix $\Sigma^0$ is approximately sparse (each row has bounded absolute sum, Assumption 1).

**Correlation of the corrected values.** The covariance of the $y$'s has $\sigma_{lm} = (1 - \tfrac1n)\sigma^0_{lm}$ off the diagonal and $\sigma_{ll} = (1 - \tfrac1n)(\sigma^0_{ll} + \sigma_e^2)$ on it, so

$$\rho_{lm} = \frac{\sigma^0_{lm}}{\sqrt{(\sigma^0_{ll} + \sigma_e^2)(\sigma^0_{mm} + \sigma_e^2)}} \ \approx \ \rho^0_{lm} \qquad \text{when } \sigma_e^2 \ll \sigma^0_{ll}.$$

**Theorem (concentration).** Let $R_n$ be the matrix of pairwise-complete Pearson correlations of the $\hat y_{ij}$, computed for each pair $(l,m)$ over the samples where both taxa are present. If $\Sigma^0$ satisfies the sparsity assumption and every taxon and every pair of taxa is present with probability bounded below by some $\delta_{\min} > 0$, then

$$\| R_n - R \|_{\max} = O_p\!\left(\sqrt{\frac{\log d}{n}}\right).$$

The same rate holds for the Spearman version computed from ranks of $\hat y_{ij}$.

## Expansion

The additive log-scale model turns the two unknown biases into row and column effects. Column effects vanish on centering. The row effect is common to every present taxon of sample $i$, while the signal terms $a_{ij} - \bar a_{\cdot j}$ average to approximately zero over many taxa when correlations are sparse, so a per-sample average of centered values isolates the bias. Once both effects are removed, correlations among the corrected values differ from those of the absolute abundances only through the measurement-noise inflation of the variances. The $\sqrt{\log d / n}$ rate follows from sub-Gaussian (Hoeffding-type, for ranks) tail bounds applied entrywise and a union bound over the $d^2$ pairs; sparsity of the final estimate is obtained by thresholding or $p$-value filtering, and a distance-correlation analogue captures nonlinear dependence.

## Sources

- H. Lin, M. Eggesbø and S. D. Peddada, "Linear and nonlinear correlation estimators unveil undescribed taxa interactions in microbiome data", Nature Communications 13 (2022), 4946, Methods (SECOM model set-up, Eqs. (1)–(8), Assumptions 1–3, Theorems 1–2), <https://doi.org/10.1038/s41467-022-32243-x>, PMCID: PMC9399263.
