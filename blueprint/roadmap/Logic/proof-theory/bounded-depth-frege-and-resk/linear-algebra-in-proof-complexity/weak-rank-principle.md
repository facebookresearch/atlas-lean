# The weak rank principle

The weak rank principle WRank says that for $m>n$, with $m$ arbitrarily larger than $n$, symbolic matrices $X$ ($m\times n$) and $Y$ ($n\times m$) cannot satisfy $XY=A$ for a scalar matrix $A$ of rank greater than $n$. It is an algebraic strengthening of the weak pigeonhole principle.

Let $m>n$ and let $A$ be an $m\times m$ scalar matrix of rank at least $n+1$. The *weak rank principle* states that the equation $XY=A$ is unsatisfiable for variable matrices $X=(x_{i,k})$ of dimension $m\times n$ and $Y=(y_{k,j})$ of dimension $n\times m$; "weak" refers to the regime where $m$ is arbitrarily larger than $n$, as for the weak pigeonhole principle, and lower bounds are expressed in terms of $n$ independently of $m$.

Its *algebraic encoding* $\mathrm{Rank}^m_n(A)$ (the negation of WRank) is the system of $m^2$ degree-2 polynomial equations

$$
\sum_{k=1}^{n}x_{i,k}\,y_{k,j}=A_{i,j}\qquad(i,j\in[m]).
$$

Two CNF encodings are also used. The *perfect matching encoding* $\mathrm{PMRank}^m_n(A)$ encodes each equation by asserting a perfect matching on its satisfied monomials $x_{i,k}y_{k,j}$, using extension variables for pairs of monomials and an extra point when $A_{i,j}=1$. The *bamboo-tree encoding* $\mathrm{BTRank}^m_n(A)$ computes each inner product sequentially: an extension variable $z_{i,j,k}$ stands for the monomial $x_{i,k}y_{k,j}$ and $u_{i,j,\ell}$ for the partial sum $\sum_{k=1}^{\ell}x_{i,k}y_{k,j}$, arranged as a totally unbalanced binary tree.

## Expansion

When the matrix product is read as a map $G(X,Y)=XY$ from $2mn$ bits to $m^2$ bits, $\mathrm{Rank}^m_n(A)$ says that $A$ is outside the image of $G$, so lower bounds for every $A$ make WRank a *proof complexity generator*. WRank subsumes the weak pigeonhole principle and systems of linear equations, which is why it admits lower bounds where those fail. For the strong rank principle ($m=n+1$, and up to $m\le n^2$) size lower bounds for polynomial calculus resolution follow from the pigeonhole principle, but for arbitrary $m$ only degree lower bounds were known; for resolution, weak pigeonhole lower bounds with any number of pigeons are known ([Raz-Razborov](../../resolution-separations-and-supercritical-tradeoffs/weak-php-resolution.md)). The best known upper bound for WRank is a polynomial-size NC$^2$-Frege proof: in strong enough systems WRank follows from the case $A=I$, which follows from the inversion principle, which has [polynomial-size NC$^2$-Frege proofs](nc2-frege-determinant-and-inversion.md).

## Depends on

None.

## Proof depends on

None.

## Sources

- Michal Garlík, Svyatoslav Gryaznov, Hanlin Ren and Iddo Tzameret, "The Weak Rank Principle: Lower Bounds and Applications", *58th Annual ACM Symposium on Theory of Computing (STOC 2026)*, 2026, https://doi.org/10.1145/3798129.3800735; numbering as in arXiv:2608.08760v1 (Section 1, the weak rank principle; Section 2.1, algebraic, perfect matching and bamboo-tree encodings).
