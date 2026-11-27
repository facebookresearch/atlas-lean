# The genetic relationship matrix is positive semidefinite

For natural numbers $N$ and $M$ and every real $N \times M$ matrix $X$ (genotypes of $N$
individuals at $M$ markers, not necessarily standardized), the
[genetic relationship matrix](grm.md) $A = XX^\top / M$, with entries
$A_{ij} = \frac{1}{M} \sum_k X_{ik} X_{jk}$, is positive semidefinite: it is symmetric and
$v^\top A v \ge 0$ for every $v \in \mathbb{R}^N$. For $M = 0$ it is the zero matrix, by the
convention $x / 0 = 0$.
