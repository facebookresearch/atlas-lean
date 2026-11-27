# Freeman-Tukey variance-stabilizing transform for Poisson counts

For a count $X \sim \mathrm{Poisson}(\lambda)$ with $\lambda > 0$, the Freeman-Tukey transform is

$$\mathrm{FT}(X) = \sqrt{X} + \sqrt{X + 1}.$$

Its variance is asymptotically independent of the mean:

$$\operatorname{Var}\bigl(\mathrm{FT}(X)\bigr) \to 1 \quad (\lambda \to \infty), \qquad \mathbb{E}\bigl[\mathrm{FT}(X)\bigr] = 2\sqrt{\lambda} + O(\lambda^{-1/2}),$$

whereas $\operatorname{Var}(X) = \lambda$ grows with the mean. In single-cell copy-number inference the transformed counts are further log-transformed, $\log\bigl(\sqrt{X} + \sqrt{X+1}\bigr)$, before smoothing along the genome.

## Remarks

By the delta method, $\sqrt{X}$ has variance about $1/4$ for large $\lambda$; $\sqrt{X+1}$ is almost perfectly correlated with it, so the sum has variance about $4 \cdot 1/4 = 1$. Compared with the plain square root, the second term improves the approximation at small means and maps $X = 0$ to $1$ rather than $0$, which matters for sparse single-cell UMI counts where most entries are zero. Equalizing variance across highly and lowly expressed genes lets a single smoothing model (a polynomial dynamic linear model in the source) and a single segmentation cutoff serve the whole genome.

## Sources

- R. Gao et al., "Delineating copy number and clonal substructure in human tumors from single-cell transcriptomes", Nature Biotechnology 39 (2021) 599-608, Methods, "Preprocessing and transformation of scRNA-seq data". <https://doi.org/10.1038/s41587-020-00795-2> (PMC8122019)
- M. F. Freeman, J. W. Tukey, "Transformations related to the angular and the square root", Annals of Mathematical Statistics 21(4) (1950) 607-611. <https://doi.org/10.1214/aoms/1177729756>
