# Sensitivity of a matrix factorization

Let $n, k, d \ge 1$, let $C \in \mathbb{R}^{k \times n}$, and let $\gamma = \max_{1 \le i \le n} \|C_{:,i}\|_2$ be the largest Euclidean norm of a column of $C$. The maximum is over a nonempty set because $n \ge 1$. Fix $\zeta \ge 0$. Two data matrices $G, H \in \mathbb{R}^{n \times d}$ are *neighbouring* when they differ in a single row and the Euclidean norm of the difference of that row is at most $\zeta$. Then for neighbouring $G, H$,

$$
\|CG - CH\|_F \;\le\; \gamma\,\zeta .
$$

For matrices in standard Euclidean coordinates, $\|M\|_F = (\sum_{i,j} M_{ij}^2)^{1/2}$.

## Proof sketch

If $G$ and $H$ differ only in row $i$, then $CG - CH = C_{:,i}\,(g_i - h_i)^{\mathsf T}$. This is a rank-one matrix whose Frobenius norm is $\|C_{:,i}\|_2\,\|g_i - h_i\|_2 \le \gamma\zeta$. If $G = H$, both sides are bounded trivially.

## Depends on

- [Frobenius norm](../../../Analysis/partial-differential-equations/hessian-estimates-for-the-equation/frobenius-norm.md)

## Proof depends on

No further prerequisites: the proof is a direct computation from the definitions above.

## Sources

- C. A. Choquette-Choo, H. B. McMahan, K. Rush and A. Thakurta, "Multi-Epoch Matrix Factorization Mechanisms for Private Machine Learning", ICML 2023, arXiv:2211.06530v2, Appendix H.1, Theorem H.1 under its condition 1 with one participation, Eq. (10): a matrix with one column of norm at most $1$, times a one-row matrix whose row has norm at most $1$, has Frobenius norm at most $1$, with no restriction on the number of rows. Apply it to the column $C_{:,i}/\gamma$ and the row $(g_i - h_i)^{\mathsf T}/\zeta$; if $\gamma = 0$ the difference $CG - CH$ is $0$, and if $\zeta = 0$ neighbouring matrices are equal.
- S. Denisov, H. B. McMahan, K. Rush, A. Smith and A. Thakurta, "Improved Differential Privacy for SGD via Optimal Private Linear Operators on Adaptive Streams", NeurIPS 2022, arXiv:2202.08312v3, Definition 3.1 (neighbouring data matrices) and Theorem 3.1 (the maximum column norm $\gamma$ for square factors).
