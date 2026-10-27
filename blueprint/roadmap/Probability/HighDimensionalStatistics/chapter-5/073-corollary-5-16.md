---
article_id: af_1f2f59ab1b246b799ccaf039
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MinimaxL1Ball.cor_5_16
---

# Corollary 5.16

Recall that $\mathcal{B}_1(R) \subset \mathbb{R}^d$ denotes the set of vectors $\theta \in \mathbb{R}^d$ such that $|\theta|_1 \leq R$. Then there exists a constant $C > 0$ such that if $d \geq n^{1/2+\varepsilon}$, $\varepsilon > 0$, the minimax rate of estimation over $\mathcal{B}_1(R)$ in the Gaussian sequence model is $\phi(\mathcal{B}_1(R)) = \min(R^2,\, R\sigma \log d / n)$. Moreover, it is attained by the constrained least squares estimator $\hat{\theta}_{\mathcal{B}_1(R)}^{\mathrm{LS}}$ if $R \geq \sigma \log d / n$ and by the trivial estimator $\hat{\theta} = 0$ otherwise.

## Depends on

- [Definition 5.1](../section-5/059-definition-5-1.md)

## Proof depends on

- [Theorem 5.11](../section-5/068-theorem-5-11.md)
- [Lemma 5.14 (Sparse Varshamov-Gilbert)](../section-5/071-sparse-varshamov-gilbert.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 5](../../../../sources/v1/HighDimensionalStatistics.md)
