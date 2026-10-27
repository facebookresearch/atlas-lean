---
article_id: af_c2fe4530ca4754bc4e8ec982
declaration: theorem
origin: cited
lean: kolmogorov_three_series_theorem
---

# Theorem (Kolmogorov three-series theorem)

Let $X_1, X_2, \ldots$ be independent and fix $A > 0$. Write $Y_i = X_i \mathbf{1}_{(|X_i| \leq A)}$. Then $\sum X_i$ converges a.s. if and only if the following are all true: (1) $\sum_{n=1}^{\infty} P(|X_n| > A)$ converges, (2) $\sum_{n=1}^{\infty} E[Y_n]$ converges, (3) $\sum_{n=1}^{\infty} \operatorname{Var}(Y_n) < \infty$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [First Borel-Cantelli lemma](../lecture-9/021-first-borel-cantelli-lemma.md)
- [Theorem (Kolmogorov zero-one law)](024-kolmogorov-zero-one-law.md)
- [Theorem (Kolmogorov maximal inequality)](025-kolmogorov-maximal-inequality.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 10, Kolmogorov three-series theorem](../../../../../sources/v1/TheoryOfProbability.md)
