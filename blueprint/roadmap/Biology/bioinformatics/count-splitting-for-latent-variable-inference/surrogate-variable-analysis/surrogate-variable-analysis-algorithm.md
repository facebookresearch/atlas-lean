# Surrogate variable analysis algorithm

In the [surrogate variable model](surrogate-variable-model-of-expression-heterogeneity.md), surrogate variables are estimated in two stages.

**Detection of unmodeled factors.**
1. Fit $x_{ij} = \mu_i + f_i(y_j) + e_{ij}$ by least squares and form the residual matrix $R \in \mathbb{R}^{m\times n}$, $r_{ij} = x_{ij} - \hat\mu_i - \hat f_i(y_j)$.
2. Compute the [singular value decomposition](../../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/singular-value-decomposition-theorem/real-singular-value-decomposition.md) $R = U D V^\top$ with singular values $d_1 \ge d_2 \ge \dots$. If the fit uses $\mathrm{df}$ degrees of freedom, the last $\mathrm{df}$
   singular values are zero; for $k = 1, \dots, n - \mathrm{df}$ let $T_k = d_k^2 / \sum_{\ell} d_\ell^2$, the variance fraction of the $k$-th eigengene.
3. Permute each row of $R$ independently, refit the primary-variable model to the permuted matrix to get a null residual matrix $R^0$, and
   compute its statistics $T_k^0$. Repeat $B$ times to get $T_k^{0b}$, $b = 1, \dots, B$.
4. Set $p_k = \frac1B \#\{ b : T_k^{0b} \ge T_k \}$, enforce monotonicity $p_k \leftarrow \max(p_{k-1}, p_k)$, and call eigengene $k$ significant
   if $p_k \le \alpha$. Let $\hat K$ be the number of significant eigengenes.

**Construction of surrogate variables.** For each significant residual eigengene $e_k$ (the $k$-th column of $V$), $k = 1, \dots, \hat K$:
1. Regress $e_k$ on each gene's expression $x_i$ and compute p-values for association; estimate the null proportion $\hat\pi_0$ and keep the
   $\hat m_k = \lfloor (1 - \hat\pi_0) m \rfloor$ genes with the smallest p-values.
2. Form the reduced $\hat m_k \times n$ matrix $X_r$ of these genes' **original** expression and compute its eigengenes $e^r_1, \dots, e^r_n$.
3. Set $\hat h_k = e^r_{j^*}$, where $j^*$ is the smallest index maximizing the **absolute** correlation $\lvert\operatorname{cor}(e^r_j, e_k)\rvert$
   over the eigengenes $e^r_j$ with nonzero singular value. Singular vectors are determined only up to sign, and the absolute value makes
   the choice of $j^*$, hence the span of $\hat h_k$, independent of those signs; the sign of $\hat h_k$ itself is immaterial, since only
   its span enters the final fit. (The source's "most correlated" eigengene leaves orientation unspecified; with signed correlation,
   reversing the target eigengene would change which eigengene is selected.)

Finally fit $x_{ij} = \mu_i + f_i(y_j) + \sum_{k=1}^{\hat K} \lambda_{ki} \hat h_{kj} + e_{ij}$ with gene-specific coefficients $\lambda_{ki}$ and
test the primary variable in this model.

## Depends on

- [Surrogate variable model of expression heterogeneity](surrogate-variable-model-of-expression-heterogeneity.md)
- [Real singular value decomposition](../../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/singular-value-decomposition-theorem/real-singular-value-decomposition.md)

## Expansion

The permutation null destroys gene-gene dependence row by row, so $T_k^0$ calibrates how much variance an eigengene explains by chance;
monotone p-values reflect that a later eigengene cannot be significant without the earlier ones. Building $\hat h_k$ from the original data
of the genes driving residual signature $k$, rather than from the residuals, lets a surrogate variable be correlated with the primary
variable; estimating it from residuals would force orthogonality and bias tests of the primary variable. (Leek and Storey 2007,
Materials and Methods, "Algorithm to detect unmodeled factors" and "Algorithm to construct surrogate variables".)

## Sources

- J. T. Leek and J. D. Storey, "Capturing Heterogeneity in Gene Expression Studies by Surrogate Variable Analysis", PLoS Genetics (2007), <https://doi.org/10.1371/journal.pgen.0030161> (PMC1994707).
