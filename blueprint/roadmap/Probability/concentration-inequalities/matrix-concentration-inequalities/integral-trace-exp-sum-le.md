# Subadditivity of matrix cumulant generating functions

Let $X_0, \dots, X_{N-1}$ be independent random Hermitian $d \times d$ complex matrices on a probability space and $\theta \in \mathbb{R}$. Assume that the entries of each $e^{\theta X_k}$ and the trace $\operatorname{tr} e^{\theta \sum_k X_k}$ are integrable. Then

$$\mathbb{E}\operatorname{tr}\exp\Big(\theta \sum_k X_k\Big) \le \operatorname{tr}\exp\Big(\sum_k \log \mathbb{E}\, e^{\theta X_k}\Big).$$

In terms of the matrix cgfs $\Xi_{X}(\theta) = \log \mathbb{E}\, e^{\theta X}$ this reads $\operatorname{tr}\exp \Xi_{\sum_k X_k}(\theta) \le \operatorname{tr}\exp \sum_k \Xi_{X_k}(\theta)$, a matrix substitute for the additivity of scalar cgfs. The proof applies Lieb's theorem once per summand, conditioning on the others.

## Informally uses

- [Lieb's concavity theorem](../../../LinearAlgebra/positive-definite-matrices/lieb-s-concavity-theorem/lieb-concavity.md): the concavity used, through Jensen's inequality, for each summand.

## Sources

- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, Lemma 3.5.1, display (3.5.1).
- J. A. Tropp, User-friendly tail bounds for sums of random matrices, Found. Comput. Math. 12 (2012), 389–434, arXiv:1004.4389, Lemma 3.4.
