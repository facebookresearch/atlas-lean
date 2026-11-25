# Best low-rank approximation in a Kronecker covariance norm

Let $F\in\mathbb R^{n\times r}$, and let $V_1\in\mathbb R^{n\times n}$ and $V_2\in\mathbb R^{r\times r}$ be symmetric positive definite. Write $S_a=V_a^{1/2}$ for their symmetric positive definite square roots, so $S_a$ is invertible and $S_a^2=V_a$. For every $X\in\mathbb R^{n\times r}$, with $\operatorname{vec}$ stacking columns,

$$\|X\|_V^2:=\operatorname{tr}(V_1^{-1}XV_2^{-1}X^{\mathsf T})=\operatorname{vec}(X)^{\mathsf T}(V_2\otimes V_1)^{-1}\operatorname{vec}(X)=\|S_1^{-1}XS_2^{-1}\|_F^2.$$

Let $\widetilde F=S_1^{-1}FS_2^{-1}$ and let $\widetilde F_k$ be a [truncated SVD](trunc-svd.md) retaining its $k$ largest singular values. List these values as $\widetilde\sigma_0\ge\widetilde\sigma_1\ge\cdots$, padded by zero beyond $\min(n,r)$. For every natural $k$,

$$\min_{\operatorname{rank}G\le k}\|F-G\|_V^2=\sum_{i\ge k}\widetilde\sigma_i^2,\qquad G^*=S_1\widetilde F_kS_2\text{ attains the minimum}.$$

For $k=0$, $G^*=0$ and the minimum is $\|F\|_V^2$. For $k\ge\min(n,r)$, $G^*=F$ and the minimum is zero. Empty row or column shapes are the trivial zero-matrix case. No general uniqueness assertion is made: a positive singular-value tie across the truncation cutoff can give multiple minimizers.

## Norm identification and application of the prerequisite

Symmetry of the roots and cyclicity of trace give

$$\|S_1^{-1}XS_2^{-1}\|_F^2=\operatorname{tr}(S_1^{-1}XV_2^{-1}X^{\mathsf T}S_1^{-1})=\operatorname{tr}(V_1^{-1}XV_2^{-1}X^{\mathsf T}).$$

The column-stacking identity $\operatorname{vec}(PXQ)=(Q^{\mathsf T}\otimes P)\operatorname{vec}(X)$ gives the quadratic-form equality. The map $G\mapsto S_1^{-1}GS_2^{-1}$ is a rank-preserving bijection, with inverse $H\mapsto S_1HS_2$. Apply the [Eckart–Young theorem](is-least-frobenius-sub-sq.md) to $\widetilde F$ and pull back the truncated minimizer. This reduction discharges the strict-SPD hypotheses and identifies the covariance norm; it is not a new whitening theorem for arbitrary invertible factors.

The order $V_2\otimes V_1$ follows from column stacking, not from ordinary commutation of the factors. Even commuting diagonal factors can distinguish the two orders. With $V_1=\operatorname{diag}(9,1)$, $V_2=\operatorname{diag}(4,1)$ and $X=\left(\begin{smallmatrix}0&1\\0&0\end{smallmatrix}\right)$, the correct quadratic form is $1/9$, whereas replacing the covariance by $V_1\otimes V_2$ while retaining the same vectorization gives $1/4$. For differently sized factors, ordinary matrix commutation is not even defined.

## Worked application

Take $F=\operatorname{diag}(6,2)$, $V_1=\operatorname{diag}(9,1)$ and $V_2=\operatorname{diag}(4,1)$. Then $\widetilde F=\operatorname{diag}(1,2)$. The weighted minima at ranks $0,1,2$ are respectively $5,1,0$, with rank-one optimizer $G^*=\operatorname{diag}(0,2)$. The corresponding unweighted minima are $40,4,0$. The unweighted rank-one choice $\operatorname{diag}(6,0)$ has weighted cost $4$, not the optimum $1$.

Strict positive definiteness and the separable covariance are essential to this reduction. For a general covariance on column-vectorized matrices, vector whitening need not preserve matrix rank: covariance $\operatorname{diag}(1,1,1,1/4)$ whitens the rank-one all-ones $2\times2$ matrix to $\left(\begin{smallmatrix}1&1\\1&2\end{smallmatrix}\right)$, of rank two. This is not a claim that every non-Kronecker problem lacks a closed form. No singular-covariance or pseudoinverse extension is asserted. A low-rank matrix fit is not by itself an admixture-graph model or a calibrated rank test.

## Depends on

- [Truncated singular value decomposition](trunc-svd.md)

## Proof depends on

- [Eckart–Young, best-approximation form](is-least-frobenius-sub-sq.md)

## Expansion

- The existence, symmetry and invertibility of the positive definite square roots, the trace and column-stacking identities, the displayed minimizer and the worked application.

## Sources

- C. Eckart and G. Young, "The approximation of one matrix by another of lower rank", *Psychometrika* 1 (1936), 211–218, <https://doi.org/10.1007/BF02288367>, for the underlying approximation theorem. The norm and root specialization above reduces the statement to that theorem.
- É. Harney, N. Patterson, D. Reich and J. Wakeley, "Assessing the performance of qpAdm: a statistical tool for studying population admixture", *Genetics* 217 (2021), iyaa045, <https://doi.org/10.1093/genetics/iyaa045>, rank-based motivation only, not a proof of this statement or a test-calibration claim.
