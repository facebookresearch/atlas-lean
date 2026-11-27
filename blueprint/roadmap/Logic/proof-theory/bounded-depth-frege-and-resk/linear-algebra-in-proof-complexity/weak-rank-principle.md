# The weak rank principle

The weak rank principle WRank says that for $m>n$, with $m$ arbitrarily larger than $n$, an $m\times m$ matrix $A$ over a field $\mathbb F$ of rank greater than $n$ is not a product $XY$ of an $m\times n$ and an $n\times m$ matrix over $\mathbb F$. It is an algebraic strengthening of the weak pigeonhole principle.

Fix a field $\mathbb F$ (the *expressed field*), integers $m>n$, and an arbitrary matrix $A\in\mathbb F^{m\times m}$. The *rank principle* $\mathrm{Rank}^m_n(A)$ (the negation of WRank) is the system of $m^2$ degree-2 polynomial equations

$$
\sum_{k=1}^{n}x_{i,k}\,y_{k,j}=A_{i,j}\qquad(i,j\in[m])
$$

in the $2mn$ variables of $X=(x_{i,k})\in\mathbb F^{m\times n}$ and $Y=(y_{k,j})\in\mathbb F^{n\times m}$; it says $XY=A$. By linear algebra it is unsatisfiable over $\mathbb F$ when the rank of $A$ over $\mathbb F$ exceeds $n$, and WRank is the statement of this unsatisfiability. "Weak" refers to the regime where $m$ is arbitrarily larger than $n$, as for the weak pigeonhole principle, and lower bounds are expressed in terms of $n$ independently of $m$. The *algebraic encoding* is $\mathrm{Rank}^m_n(A)$ itself.

The two CNF encodings take $\mathbb F=\mathbb F_2$ and $A\in\{0,1\}^{m\times m}$, so all variables are Boolean and each equation states the parity of the satisfied monomials $x_{i,k}y_{k,j}$; the field of the proof system refuting them is a separate parameter.

- The *perfect matching encoding* $\mathrm{PMRank}^m_n(A)$ encodes each equation by asserting a perfect matching on its satisfied monomials: if $A_{i,j}=0$ it has variables $z_{i,j,\{k,\ell\}}$ for pairs $\{k,\ell\}\subseteq[n]$, and clauses saying that every satisfied monomial $x_{i,k}y_{k,j}$ is matched by exactly one $z_{i,j,\{k,\ell\}}$ to another satisfied monomial; if $A_{i,j}=1$ it has variables $w_{i,j,\{k,\ell\}}$ for pairs $\{k,\ell\}\subseteq[n+1]$, with the same clauses over the satisfied monomials together with one extra point $n+1$, which must be matched.
- The *bamboo-tree encoding* $\mathrm{BTRank}^m_n(A)$ computes each inner product sequentially: an extension variable $z_{i,j,k}$ stands for the monomial $x_{i,k}y_{k,j}$ and $u_{i,j,\ell}$ for the partial sum $\sum_{k=1}^{\ell}x_{i,k}y_{k,j}$ over $\mathbb F_2$, with clauses for $z_{i,j,k}=x_{i,k}y_{k,j}$, $u_{i,j,1}=z_{i,j,1}$, $u_{i,j,\ell}=u_{i,j,\ell-1}+z_{i,j,\ell}$ and $u_{i,j,n}=A_{i,j}$, arranged as a totally unbalanced binary tree.

## Expansion

Read the matrix product as the map $g(X,Y)=XY$ from $\mathbb F_2^{2mn}$ to $\mathbb F_2^{m^2}$. The equations of $\mathrm{Rank}^m_n(A)$ assert that $A$ has a preimage under $g$, so their unsatisfiability asserts that $A$ is outside the range of $g$; lower bounds for every $A$ therefore make WRank a *proof complexity generator*, which stretches its input when $m>2n$. WRank subsumes the weak pigeonhole principle and systems of linear equations, which is why it admits lower bounds where those fail. For the strong rank principle ($m=n+1$, and up to $m\le n^2$) size lower bounds for polynomial calculus resolution follow from the pigeonhole principle, but for arbitrary $m$ only degree lower bounds were known; for resolution, weak pigeonhole lower bounds with any number of pigeons are known ([Raz-Razborov](../../resolution-separations-and-supercritical-tradeoffs/weak-php-resolution.md)). The best known upper bound for WRank is a polynomial-size NC$^2$-Frege proof: in strong enough systems WRank follows from the case $A=I$, which follows from the inversion principle, which has [polynomial-size NC$^2$-Frege proofs](nc2-frege-determinant-and-inversion.md).

## Depends on

None.

## Proof depends on

None.

## Sources

- Michal Garlík, Svyatoslav Gryaznov, Hanlin Ren and Iddo Tzameret, "The Weak Rank Principle: Lower Bounds and Applications", *58th Annual ACM Symposium on Theory of Computing (STOC 2026)*, 2026, https://doi.org/10.1145/3798129.3800735; numbering as in arXiv:2608.08760v1 (Section 1, the weak rank principle; Section 2.1, expressed and ground fields; Section 4.8, the rank principle over a field; Section 5, the rank generator and its stretch; Definition 5.8, $\mathrm{PMRank}^m_n(A)$; Definition 5.19, $\mathrm{BTRank}^m_n(A)$).
