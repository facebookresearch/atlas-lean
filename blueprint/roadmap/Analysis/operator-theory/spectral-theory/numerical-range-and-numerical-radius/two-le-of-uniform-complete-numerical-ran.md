# No uniform complete numerical-range bound has constant below two

Suppose $c$ is real
and for every pair of positive matrix sizes $n,m$, degree $d\ge 0$, complex matrix $A$ of size
$n$, and complex matrix coefficients $B_0,\ldots,B_d$ of size $m$, the Euclidean operator norm
of $\sum_{k=0}^d A^k\otimes B_k$ is at most $c$ times the supremum of the Euclidean operator
norm of $\sum_{k=0}^d z^k B_k$ on the numerical range of $A$. The numerical range here uses
$\langle x,Ax\rangle$ for unit vectors $x$, with the inner product linear in its second
argument. Then $2\le c$. The bound from below is independent of the upper-bound theorem.

## Sources

- OpenAI, *A direct proof of the complete Crouzeix inequality*, [sharpness statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DirectCrouzeix.lean#L27-L39).
