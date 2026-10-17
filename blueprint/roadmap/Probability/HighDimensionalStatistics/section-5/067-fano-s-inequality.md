---
article_id: af_9cd746ea0247015284e0eadb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: FanoInequality.fano_inequality
---

# Theorem 5.10 (Fano's inequality)

Let $P_1, \ldots, P_M$, $M \geq 2$ be probability distributions such that $P_j \ll P_k$ for all $j, k$. Then $$\inf_{\psi} \max_{1 \leq j \leq M} P_j\!\left[\psi(X) \neq j\right] \geq 1 - \frac{\frac{1}{M^2} \sum_{j,k=1}^{M} \mathsf{KL}(P_j, P_k) + \log 2}{\log(M - 1)}$$ where the infimum is taken over all tests with values in $\{1, \ldots, M\}$.

## Depends on

- [Definition 5.5](063-definition-5-5.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 5.4](../../../../sources/v1/HighDimensionalStatistics.md)
