# Contiguous layout of a fully allocated van Emde Boas tree

Lay out a depth-$d$ van Emde Boas record as a five-word header (presence, minimum, maximum, split size, child span) followed, for $d \ge 1$, by the summary record and the $u_{d-1}$ cluster records of depth $d - 1$, all fully allocated. Its size $\mathrm{span}(d)$ satisfies $\mathrm{span}(d) = 5 + (1 + u_{d-1})\, \mathrm{span}(d-1)$ for $d \ge 1$ and $\mathrm{span}(d) \le 10\, u_d$. All subrecords lie within their parent and do not overlap, so the whole tree occupies $O(u)$ contiguous words.

## Proof sketch

Write $\rho_d = \mathrm{span}(d) / u_d$. Since $u_d = u_{d-1}^2$, the recurrence gives $\rho_d = (1 + 1/u_{d-1}) \rho_{d-1} + 5/u_d$, starting from $\rho_0 = 5/2$. Because $u_d$ grows doubly exponentially, the product $\prod_k (1 + 1/u_k)$ and the sum $\sum_k 5/u_k$ converge quickly, and direct computation of the first terms ($\rho_1 = 5$, $\rho_2 < 6.6$, $\rho_3 < 7$) shows $\rho_d < 10$ for all $d$.

## Depends on

- [Recursive van Emde Boas tree with excluded minimum](recursive-van-emde-boas-tree.md)

## Sources

- E. D. Demaine, "Lecture 4: Divide and Conquer: van Emde Boas Trees", 6.046J Design and Analysis of Algorithms, MIT OpenCourseWare, 2015.
- P. van Emde Boas, R. Kaas and E. Zijlstra, "Design and Implementation of an Efficient Priority Queue", Mathematical Systems Theory 10, 1977.
