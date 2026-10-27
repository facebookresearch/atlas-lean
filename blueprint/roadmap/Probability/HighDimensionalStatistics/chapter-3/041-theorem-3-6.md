---
article_id: af_4e2dbaa75374ac9e3f2693f3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Chapter3.theorem_3_6_maurey
---

# Theorem 3.6

Let $\{\varphi_1, \ldots, \varphi_M\}$ be a dictionary normalized in such a way that $\max_{1 \leq j \leq M} |\varphi_j|_2 \leq D\sqrt{n}$. Then for any integer $k$ such that $1 \leq k \leq M$ and any positive $R$, we have $$\min_{\theta \in \mathbb{R}^M,\, |\theta|_0 \leq 2k} \mathsf{MSE}(\varphi_\theta) \leq \min_{\theta \in \mathbb{R}^M,\, |\theta|_1 \leq R} \mathsf{MSE}(\varphi_\theta) + D^2 R^2 / k.$$

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 3, Section 3.1](../../../../sources/v1/HighDimensionalStatistics.md)
