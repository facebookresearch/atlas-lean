---
article_id: af_7b8c63d09518584ce6506c3e
declaration: theorem
origin: cited
statement: formalized
lean: BrownianFDD.brownian_fdd_convergence
---

# Theorem 1 (Chapter 1 (Brownian Motion))

Let $0 \leq t_0 < t_1 < t_2 < \cdots < t_m$ and let $I_1 \times I_2 \times \cdots \times I_m \subset \mathbb{R}^m$ be a rectangle (product of intervals). Let $\sigma_j > 0$ be such that $\sigma_j^2 = t_j - t_{j-1}$. Then $$\lim_{n \to \infty} P[(f_n(t_1) - f_n(t_0), f_n(t_2) - f_n(t_1), \ldots, f_n(t_m) - f_n(t_{m-1})) \in I_1 \times \cdots \times I_m] = \int_{I_1 \times \cdots \times I_m} \prod_{j=1}^m g_{\sigma_j}(x_j) \, dx_1 \cdots dx_m$$

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 2 (Central Limit Theorem)](../section-2/021-central-limit-theorem.md)

## Sources

- [MIT 18.103 Fourier Analysis (Fall 2013), Chapter 1 (Brownian Motion)](../../../../sources/v1/FourierAnalysis.md)
