# Polynomial bit-length bounds for exact rational elimination

For an $m \times n$ rational matrix $A$ and a rational vector $b$ whose entries have numerators and denominators of absolute value at most $2^{\beta}$, multiply each row of $[A \mid b]$ by the product of the denominators of its $n + 1$ entries, giving an integer matrix with entries of absolute value at most $2^{(n+1)\beta}$. Fraction-free elimination on this matrix computes the reduced row echelon form and rank of $A$ and (for a consistent system $Ax = b$) a rational solution, and every entry it produces is, up to sign, a minor of order at most $n + 1$ of the cleared matrix, so it has absolute value at most $(n+1)! \, 2^{(n+1)^2\beta}$, a bit length of $O(n^2\beta + n\log n)$; each numerator before an exact division is a pivot times such a minor. In particular all intermediate numbers have bit length polynomial in the input size, and Gaussian elimination over $\mathbb{Q}$ runs in polynomial time (Schrijver, Chapter 3).

## Proof sketch

Clear denominators row by row: each cleared entry is a numerator times at most $n$ denominators. Sylvester's identity identifies each intermediate entry with a minor of order $k \le n + 1$ of the cleared matrix, and expanding the determinant bounds such a minor by $k! \, (2^{(n+1)\beta})^k$.

## Depends on

- [Fraction-free (Bareiss-Jordan) elimination](bareiss-fraction-free-elimination.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Sources

- A. Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
- E. H. Bareiss, "Sylvester's Identity and Multistep Integer-Preserving Gaussian Elimination", Mathematics of Computation 22(103), 1968.
