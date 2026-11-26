# Coverage-controlled imputation error bound

Let $G_j$ be the dosage at dense locus $j$ with variance $\sigma_j^2$, let $\hat G_j(S)$ be its least-squares linear imputation from the typed panel $S$, and let $R_j^2(S)$ be the corresponding coefficient of determination. If the recoverability scores are calibrated in the sense that

$$R_j^2(S) \ge \max_{i\in S} q_{ij} \quad \text{for every } j,$$

then for any weights $w_j \ge 0$

$$\sum_{j=1}^p w_j\,\mathbb{E}\left(G_j - \hat G_j(S)\right)^2 \le \sum_{j=1}^p w_j\sigma_j^2\left(1 - \max_{i\in S} q_{ij}\right)$$

(Xu and Tan 2026, Proposition 1). Thus raising facility-location coverage lowers an upper envelope on weighted imputation error, but only under the calibration assumption, which empirical correlation proxies need not satisfy.

Downstream, ridge genomic prediction is stable under imputation error: with $A = X^\top X + \lambda I$, imputed design $\tilde X = X + E$ and coefficients $\hat b$, $\tilde b$,

$$\|\tilde b - \hat b\|_2 \le \frac{\|y\|_2\|E\|_2}{\lambda} + \frac{(2\|X\|_2\|E\|_2 + \|E\|_2^2)\|X\|_2\|y\|_2}{\lambda^2}$$

(Theorem 3), so coefficient perturbations are $O(\|E\|_2)$ when $\|E\|_2$ is small relative to $\lambda/\|X\|_2$ (Corollary 1).

## Depends on

- [Monotone submodular imputation-aware panel objective](monotone-submodular-imputation-aware-panel-objective.md)
- [Closed form of ridge regression](../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/ridge-le-ridge-estimate.md)

## Expansion

For the best linear predictor, $\mathbb{E}(G_j - \hat G_j)^2 = \sigma_j^2(1 - R_j^2)$; the calibration inequality bounds $1 - R_j^2$ by $1 - \max_{i\in S}q_{ij}$, and weighting and summing gives the result. The ridge bound follows from $\tilde b - \hat b = \tilde A^{-1}(\tilde X - X)^\top y + (\tilde A^{-1} - A^{-1})X^\top y$, $\|A^{-1}\|_2, \|\tilde A^{-1}\|_2 \le 1/\lambda$ and $\tilde A - A = X^\top E + E^\top X + E^\top E$.

## Sources

- Y. Xu and X. Tan, *Imputation-aware optimization of ultra-low-density SNP panels: synthetic benchmarking and evaluation*, Plants 15(21) (2026), 3346, Proposition 1, Theorem 3 and Corollary 1. <https://doi.org/10.3390/plants15213346>
