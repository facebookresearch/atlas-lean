# Polynomial bit-length bounds for exact rational elimination

Let $M$ be an integer matrix with $q$ columns whose entries have absolute value at most $2^{\gamma}$. Fraction-free elimination on $M$ computes its rank, and every entry it produces is, up to sign, a minor of $M$ of order at most $q$ (Edmonds, Theorem 2, for Edmonds' form, which keeps each pivot row once it is used; the linked page for the Bareiss-Jordan form), so it has absolute value at most $q! \, 2^{q\gamma}$, a bit length of at most $q(\gamma + \log_2 q) + 1$ (Edmonds, p. 243 (b)); each numerator before an exact division is the previous pivot times such a minor. In the Bareiss-Jordan form, dividing each pivot row by its pivot gives the reduced row echelon form of $M$ and, for the augmented matrix of a consistent system, a rational solution, whose entries are quotients of two such minors. A rational system $Ax = b$, with $A$ of size $m \times n$ and numerators and denominators of absolute value at most $2^{\beta}$, reduces to this case by clearing denominators row by row (see the proof sketch), with $q = n + 1$ and $\gamma = (n+1)\beta$; in particular all intermediate numbers have bit length polynomial in the input size, and Gaussian elimination over $\mathbb{Q}$ runs in polynomial time.

## Proof sketch

Edmonds' Theorem 2 (or Sylvester's identity, for the Bareiss-Jordan form) identifies each entry with a minor, and expanding the determinant bounds a minor of order $k \le q$ by $k! \, (2^{\gamma})^k \le q! \, 2^{q\gamma}$ (p. 243 (b)). For rational input, multiply each row of $[A \mid b]$ by the product of the denominators of its $n + 1$ entries: each cleared entry is a numerator times at most $n$ denominators, so it has absolute value at most $2^{(n+1)\beta}$. Nonzero row scaling changes neither the rank, nor the reduced row echelon form, nor the solution set, and the bound above becomes $(n+1)! \, 2^{(n+1)^2\beta}$, a bit length of $O(n^2\beta + n\log n)$.

## Depends on

- [Fraction-free (Bareiss-Jordan) elimination](bareiss-fraction-free-elimination.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Sources

- J. Edmonds, "Systems of Distinct Representatives and Linear Algebra", Journal of Research of the National Bureau of Standards 71B(4), 1967, Section 7, Theorem 2 and p. 243 (b); open copy: <https://nvlpubs.nist.gov/nistpubs/jres/71B/jresv71Bn4p241_A1b.pdf>.
- A. Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
- E. H. Bareiss, "Sylvester's Identity and Multistep Integer-Preserving Gaussian Elimination", Mathematics of Computation 22(103), 1968.
