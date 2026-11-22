# Average Frobenius error of the randomized range finder

Let $A$ be a real $m \times n$ matrix with singular values $\sigma_1 \ge \sigma_2 \ge \cdots$ (with $\sigma_j = 0$ for $j > \min\{m, n\}$). Choose a target rank $k \ge 2$ and an oversampling parameter $p \ge 2$ with $k + p \le \min\{m, n\}$, let $\Omega$ be an $n \times (k + p)$ matrix with independent standard Gaussian entries, and let $P_Y$ be the orthogonal projection onto the range of $Y = A\Omega$. Then

$$\mathbb{E}\,\|(I - P_Y)A\|_F \le \left(1 + \frac{k}{p - 1}\right)^{1/2} \Big(\sum_{j > k} \sigma_j^2\Big)^{1/2}.$$

## Idea

To approximate a large matrix by one of low rank, the randomized range finder multiplies it by a few random vectors and projects onto the span of the results. The best possible rank-$k$ error in the Frobenius norm is $(\sum_{j > k} \sigma_j^2)^{1/2}$, by the Eckart–Young theorem, and the truncated SVD attains it. The theorem of Halko, Martinsson and Tropp says that a Gaussian sample with only $p$ extra columns comes within the factor $(1 + k/(p - 1))^{1/2}$ of that optimum on average; with $p = k + 1$ the factor is $\sqrt 2$. The method needs only matrix products, so it suits matrices too large for classical factorizations.

## Statements

- [Average Frobenius error of the randomized range finder](integral-residual-frobenius-le.md)
- [Standard Gaussian test matrix](gaussian-matrix-law.md): the Gaussian test matrix
- [Range-finder residual](residual.md): the range-finder residual
- [Frobenius error of the range finder](residual-frobenius.md): its Frobenius norm

## Background

- [Singular value decomposition](../../singular-value-decomposition/singular-value-decomposition-theorem/README.md): the error bounds are stated in terms of the singular values of $A$.

## Related topics

- [Eigenvalue inequalities and perturbation](../../../../Analysis/operator-theory/eigenvalue-inequalities/README.md)
- [Matrix concentration inequalities](../../../../Probability/concentration-inequalities/matrix-concentration-inequalities/README.md)
- [Principal component analysis](../../../../Probability/linear-models-multivariate/principal-component-analysis/README.md)
