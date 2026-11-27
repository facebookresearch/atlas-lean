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

- S. Denisov, H. B. McMahan, K. Rush, A. Smith and A. Thakurta, "Improved Differential Privacy for SGD via Optimal Private Linear Operators on Adaptive Streams", NeurIPS 2022, arXiv:2202.08312v3, Definition 3.1 (neighbouring data matrices), Theorem 3.1 ($\gamma$ is the maximum column norm of $C$, which bounds the sensitivity of $G \mapsto CG$), and equation (1) and Appendix C (rectangular factorizations, with the same rank-one norm calculation).
