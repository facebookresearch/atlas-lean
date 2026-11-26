# M-matrix

A real $n \times n$ matrix $A$ is an *M-matrix* if

1. $a_{ii} > 0$ for $i = 1, \dots, n$;
2. $a_{ij} \le 0$ for $i \ne j$;
3. $A$ is nonsingular; and
4. $A^{-1}$ has nonnegative entries.

A matrix with property 2 is a Z-matrix. The four conditions are redundant: condition 1 follows from the other three.

## Related topics

- [Nonsingular M-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-nonsingular-mmatrix.md)
- [Z-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-zmatrix.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 1.10, Definition 1.30 and the remark after it. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
