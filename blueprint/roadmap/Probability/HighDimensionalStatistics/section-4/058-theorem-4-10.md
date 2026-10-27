---
article_id: af_f45c743e55309bc325f2b51d
declaration: theorem
origin: cited
lean: Rigollet.Chapter4.Thm_4_10.theorem_4_10_textbook
---

# Theorem 4.10

Let $X_1, \ldots, X_n$ be $n$ i.i.d. copies of a sub-Gaussian random vector $X \in \mathbb{R}^d$ such that $\mathbb{E}[XX^\top] = \Sigma$ and $X \sim \mathsf{subG}_d(\|\Sigma\|_{\mathrm{op}})$. Assume further that $\Sigma = \theta vv^\top + I_d$ satisfies the spiked covariance model for $v$ such that $|v|_0 = k \leq d/2$. Then, the $k$-sparse largest eigenvector $\hat{v}$ of the empirical covariance matrix satisfies, $$\min_{\varepsilon \in \{\pm 1\}} |\varepsilon \hat{v} - v|_2 \lesssim \frac{1 + \theta}{\theta} \left(\sqrt{\frac{k \log(ed/k) + \log(1/\delta)}{n}} \vee \frac{k \log(ed/k) + \log(1/\delta)}{n}\right)$$ with probability $1 - \delta$.

## Depends on

- [Definition 1.2](../chapter-1/002-definition-1-2.md)
- [Definition 4.7](055-definition-4-7.md)

## Proof depends on

- [Definition 1.17](../section-1/017-definition-1-17.md)
- [Lemma 1.18](../section-1/018-lemma-1-18.md)
- [Lemma 2.7](../chapter-2/024-lemma-2-7.md)
- [Theorem 4.6](054-theorem-4-6.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 4.4](../../../../sources/v1/HighDimensionalStatistics.md)
