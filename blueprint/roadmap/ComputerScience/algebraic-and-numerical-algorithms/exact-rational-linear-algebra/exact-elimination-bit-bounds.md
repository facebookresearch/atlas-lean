# Polynomial bit-length bounds for exact rational elimination

Let $M$ be an integer matrix with $q$ columns whose entries have absolute value at most $2^{\gamma}$. Edmonds' fraction-free Gaussian elimination on $M$, which keeps each pivot row once it is used and divides each new entry exactly by the previous pivot, computes the rank of $M$, and every entry it produces is, up to sign, the determinant of a minor of $M$ of order at most $q$ (Edmonds, Section 7, Theorem 2). So every such entry has absolute value at most $q! \, 2^{q\gamma}$, a bit length of at most $q(\gamma + \log_2 q) + 1$, and the elimination runs in time polynomial in the numbers of rows and columns of $M$ and in $\gamma$ (Edmonds, p. 243 (b) and "The algorithm for matrices $A^0$ of integers is good").

## Proof sketch

Edmonds' Theorem 2 identifies each entry with a minor, and expanding the determinant bounds a minor of order $k \le q$ by $k! \, (2^{\gamma})^k \le q! \, 2^{q\gamma}$ (p. 243 (b)); each numerator before an exact division is the previous pivot times such a minor, so it obeys the square of the bound. The same bound holds in the Bareiss-Jordan form of the linked page, whose entries are minors by Sylvester's identity; there, dividing each pivot row by its pivot gives the reduced row echelon form of $M$ and, for the augmented matrix of a consistent system, a rational solution whose entries are quotients of two such minors. For a rational system $Ax = b$, with $A$ of size $m \times n$ and numerators and denominators of absolute value at most $2^{\beta}$, multiply each row of $[A \mid b]$ by the product of the denominators of its $n + 1$ entries: each cleared entry is a numerator times at most $n$ denominators, so it has absolute value at most $2^{(n+1)\beta}$. Nonzero row scaling changes neither the rank, nor the reduced row echelon form, nor the solution set, so the integer case applies with $q = n + 1$ and $\gamma = (n+1)\beta$: the bound becomes $(n+1)! \, 2^{(n+1)^2\beta}$, a bit length of $O(n^2\beta + n\log n)$, and Gaussian elimination over $\mathbb{Q}$ runs in polynomial time.

## Depends on

- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Fraction-free (Bareiss-Jordan) elimination](bareiss-fraction-free-elimination.md)

## Sources

- J. Edmonds, "Systems of Distinct Representatives and Linear Algebra", Journal of Research of the National Bureau of Standards 71B(4), 1967, Section 7, Theorem 2 and p. 243 (b); open copy: <https://nvlpubs.nist.gov/nistpubs/jres/71B/jresv71Bn4p241_A1b.pdf>.
- A. Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
- E. H. Bareiss, "Sylvester's Identity and Multistep Integer-Preserving Gaussian Elimination", Mathematics of Computation 22(103), 1968.
