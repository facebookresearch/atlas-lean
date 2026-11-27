# Sparse canonical correlation features for cross-tissue expression

**Setting.** For one gene, let $G \in \mathbb{R}^{n \times p_1}$ hold the standardized genotypes of $n$ individuals at $p_1$ cis-SNPs and $X \in \mathbb{R}^{n \times p_2}$ their standardized expression of that gene in $p_2$ tissues. Classical canonical correlation analysis seeks $\omega_1 \in \mathbb{R}^{p_1}$, $\omega_2 \in \mathbb{R}^{p_2}$ maximizing $\omega_1^{\mathsf T} G^{\mathsf T} X \omega_2$ subject to $\omega_1^{\mathsf T} G^{\mathsf T} G \omega_1 = \omega_2^{\mathsf T} X^{\mathsf T} X \omega_2 = 1$, which is ill-posed when $p_1 \gtrsim n$.

**Diagonal penalized (sparse) CCA** (Witten et al., as used by Feng et al. 2021, Methods "sCCA"). Replace $G^{\mathsf T} G$ and $X^{\mathsf T} X$ by the identity and add $\ell_1$ constraints:

$$\max_{\omega_1, \omega_2} \ \omega_1^{\mathsf T} G^{\mathsf T} X \omega_2 \quad \text{subject to} \quad \|\omega_1\|_2^2 \le 1,\ \|\omega_2\|_2^2 \le 1,\ \|\omega_1\|_1 \le c_1,\ \|\omega_2\|_1 \le c_2 .$$

For small $c_1, c_2$ the maximizers are sparse. The problem is solved by alternating maximization over $\omega_1$ and $\omega_2$ from an initial $\omega_2$ with $\|\omega_2\|_2 = 1$; later canonical pairs are obtained by applying the same algorithm to $G^{\mathsf T} X$ after regressing out the previous components. The penalties $c_1, c_2$ are chosen by permutation: rows of $X$ are permuted $k$ times, sCCA is run on the original and permuted data over an ordered grid of pairs, and the pair maximizing the difference between the Fisher-transformed $\mathrm{cor}(G\omega_1, X\omega_2)$ on the original data and its average on the permuted data is selected.

**Cross-tissue features.** The first three canonical pairs give three expression features $X\omega_2^{(1)}, X\omega_2^{(2)}, X\omega_2^{(3)}$, weighted averages of the gene's expression across tissues chosen to be as predictable from cis-genotype as possible.

## Depends on

- [Standardized genotype matrix](../../../ld-score-regression/is-standardized.md): the standardization of $G$ and $X$ (column sums $0$, sums of squares $n$)

## Proof depends on

- [Soft thresholding solves the one-dimensional lasso](../../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/soft-threshold-le.md): each alternating step is a soft-thresholding

## Expansion

Each feature is, by construction, the linear combination of tissue-specific expression values whose correlation with some sparse linear combination of cis-SNPs is largest, so it is selected to be cis-heritable rather than to explain expression variance; this is the difference from principal components of $X$, which maximize variance and may be dominated by non-genetic sources of cross-tissue correlation. Replacing $G^{\mathsf T}G$ and $X^{\mathsf T}X$ by the identity makes the constraints separable, so each alternating step is a soft-thresholding of $G^{\mathsf T} X \omega_2$ (respectively $X^{\mathsf T} G \omega_1$) followed by normalization, which keeps the computation feasible for $p_1$ in the thousands. Because the objective sees the pairing of genotypes with expression only through the cross-product $G^{\mathsf T} X$, while $G^{\mathsf T}G$ and $X^{\mathsf T}X$ are unchanged by reordering individuals, permuting the rows of $X$ destroys exactly the genotype–expression association, which makes the permutation scheme a calibration of the attainable canonical correlation under the null.

## Sources

- H. Feng, N. Mancuso, A. Gusev, A. Majumdar, M. Major, B. Pasaniuc and P. Kraft, "Leveraging expression from multiple tissues using sparse canonical correlation analysis and aggregate tests improves the power of transcriptome-wide association studies", PLoS Genetics 17 (2021), e1008973, Methods ("sCCA", "sCCA-TWAS"), <https://doi.org/10.1371/journal.pgen.1008973>, PMCID PMC8057593.
- D. M. Witten, R. Tibshirani and T. Hastie, "A penalized matrix decomposition, with applications to sparse principal components and canonical correlation analysis", Biostatistics 10 (2009), 515–534, <https://doi.org/10.1093/biostatistics/kxp008>.
