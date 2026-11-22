# Randomized range finder

Randomized algorithms for low-rank matrix approximation, following N. Halko, P.-G. Martinsson and J. A. Tropp, *Finding structure with randomness* (SIAM Rev. 53, 2011, [arXiv:0909.4061](https://arxiv.org/abs/0909.4061)). Multiply a real $m \times n$ matrix $A$ by a Gaussian test matrix $\Omega$ with $k + p$ columns, and project $A$ onto the range of the sample $A\Omega$. For a target rank $k \ge 2$ and an oversampling $p \ge 2$ with $k + p \le \min(m, n)$, as in the two results below, the expected error in the Frobenius norm is at most $(1 + k/(p - 1))^{1/2}$ times the best rank-$k$ error $(\sum_{j > k} \sigma_j^2)^{1/2}$, a factor close to $1$ when the oversampling $p$ is large compared with $k$. In the spectral norm the bound is $1 + \sqrt{k/(p - 1)}$ times the best error $\sigma_{k+1}$ plus a term proportional to the Frobenius norm $(\sum_{j > k} \sigma_j^2)^{1/2}$ of the tail, which no fixed multiple of $\sigma_{k+1}$ bounds.

- [Average Frobenius error of the randomized range finder](frobenius-error/README.md)
- [Average spectral error of the randomized range finder](spectral-error/README.md)

## Related topics

- [Singular value decomposition](../singular-value-decomposition/README.md)
- [Eigenvalue inequalities and perturbation](../../../Analysis/operator-theory/eigenvalue-inequalities/README.md)
- [Matrix concentration inequalities](../../../Probability/concentration-inequalities/matrix-concentration-inequalities/README.md)
- [Principal component analysis](../../../Probability/linear-models-multivariate/principal-component-analysis/README.md)
