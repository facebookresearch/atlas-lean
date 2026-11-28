# Contiguous-separating capacity of a grid code

**Setting.** Discretize one-dimensional space into positions $j\in\mathbb Z$ and encode them with $M$ grid modules of integer periods $\lambda=(\lambda_1,\dots,\lambda_M)$, as in the [modular grid code](linearly-separable-dichotomies-of-a-modular-grid-code.md). Let $J_\lambda=\operatorname{diag}(J_{\lambda_1},\dots,J_{\lambda_M})$ be the block-diagonal shift whose block $J_{\lambda_m}$ is the cyclic permutation matrix of order $\lambda_m$. The grid-cell activity matrix $A_\lambda$ has columns $c_j=J_\lambda^{\,j-1}c_1$, one per position, up to its period $L=\operatorname{lcm}(\lambda_1,\dots,\lambda_M)$. The contiguous-separating capacity $l^*$ is the largest $l$ such that every dichotomy of every $l$ contiguous positions is linearly separable (realizable by a place-cell perceptron).

**Theorem.** $l^*=\operatorname{rank}A_\lambda$, and

$$\operatorname{rank}A_\lambda=\sum_{k=1}^{M}(-1)^{k-1}\sum_{S\subset\{\lambda_1,\dots,\lambda_M\},\ |S|=k}\gcd(S).$$

For pairwise coprime periods this equals $\sum_m\lambda_m-M+1$; for example periods $\{3,4\}$ code $L=12$ positions uniquely but give $l^*=6$. On a $d$-dimensional lattice with $(\lambda_m)^d$ cells per module the capacity (as a volume) is $\sum_{k=1}^{M}(-1)^{k-1}\sum_{|S|=k}\gcd(S)^d$.

So the range over which place fields can be arranged arbitrarily scales like the sum of the grid periods, while the range of unique grid codes scales like their product.

## Depends on

- [Linearly separable dichotomies of a modular grid code](linearly-separable-dichotomies-of-a-modular-grid-code.md)

## Expansion

Take zero threshold. Contiguous columns form a Krylov sequence $c_1,J_\lambda c_1,J_\lambda^2c_1,\dots$; the dimensions $d_k$ of their spans increase by exactly one per step until they stabilize at $r=\operatorname{rank}A_\lambda$. Hence any $l\le r$ contiguous columns are linearly independent and every dichotomy of them is realizable, while $l>r$ contiguous columns are dependent and some dichotomy is not. The rank formula is an inclusion–exclusion over the common sub-periods $\gcd(S)$ shared by groups of modules.

## Sources

- M. Y. Yim, L. A. Sadun, I. R. Fiete, T. Taillefumier, "Place-cell capacity and volatility with grid-like inputs", eLife 10 (2021) e62702, Results (place-cell-separating capacity) and Appendix 3: Propositions 9, 10 and 11, Equations (64), (68) and (74), <https://doi.org/10.7554/eLife.62702>, PMCID PMC8294848.
