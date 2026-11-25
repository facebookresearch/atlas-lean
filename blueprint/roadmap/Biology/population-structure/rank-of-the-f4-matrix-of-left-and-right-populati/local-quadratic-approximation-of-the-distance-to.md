# Local quadratic approximation of the distance to a smooth submanifold

Let $W$ be a positive definite $m\times m$ matrix, $\|v\|_W^2=v^{\mathsf T}Wv$, and let $S\subseteq\mathbb R^m$ be a $C^2$ embedded submanifold near $F\in S$: there is a neighbourhood $U$ of $F$ such that $S\cap U$ is closed in $U$ and is a $C^2$ submanifold, with tangent space $T_FS$ at $F$. Write $d_W(x,S)=\inf_{s\in S}\|x-s\|_W$ and $d_W(h,T_FS)=\inf_{u\in T_FS}\|h-u\|_W$. Then

$$d_W(F+h,S)^2=d_W(h,T_FS)^2+o(\|h\|^2)\qquad(h\to0),$$

that is, for every $\eta>0$ there is $\delta>0$ with $\bigl|d_W(F+h,S)^2-d_W(h,T_FS)^2\bigr|\le\eta\|h\|^2$ for all $\|h\|<\delta$. If $S$ is an affine subspace through $F$, the two sides are equal. This is the reduction that transfers the [chi-square law of the Gaussian projection statistic](../../../Probability/linear-models-multivariate/chi-square-law-of-gaussian-projection-residuals/map-gauss-proj-stat-multivariate-gaussia.md) from linear subspaces to curved constraint sets such as rank manifolds.

For example, for the unit circle $S\subset\mathbb R^2$, $F=(1,0)$ and $W=I$, $d(F+h,S)=\bigl|\,\|F+h\|-1\bigr|$ and $d(h,T_FS)=|h_1|$, and for $\|h\|<1/2$ one has $0\le\|F+h\|-1-h_1\le h_2^2$, so the distances differ by at most $\|h\|^2$ and their squares by $O(\|h\|^3)$.

## Proof depends on

- [Implicit function theorem](../../../Analysis/real-functions/multivariable-calculus/implicit-function-theorem.md)
- [Taylor's theorem with little-o remainder in several variables](../../../Analysis/real-functions/multivariable-calculus/taylor-is-little-o-multivariable.md)

## Expansion

A proof page must establish:

- that for small $h$ the infimum over $S$ is attained near $F$, using that $S\cap U$ is closed in $U$ and $d_W(F+h,S)\le\|h\|_W$;
- a local graph representation of $S$ over $T_FS$ with a $C^2$ map whose differential vanishes at $F$, giving $|d_W(F+h,S)-d_W(h,T_FS)|=O(\|h\|^2)$ and hence the squared estimate;
- uniformity of the constants for $W$ in a compact set of positive definite matrices, which the minimum-distance chi-square limit needs;
- the affine case and the circle example with its explicit bound.

## Sources

- E. Harney, N. Patterson, D. Reich and J. Wakeley, *Assessing the performance of qpAdm: a statistical tool for studying population admixture*, Genetics 217(4) (2021), iyaa045, <https://pmc.ncbi.nlm.nih.gov/articles/PMC8049561/> (rank test; background).
