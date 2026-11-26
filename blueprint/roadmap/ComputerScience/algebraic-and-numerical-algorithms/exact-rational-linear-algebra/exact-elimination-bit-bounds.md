# Polynomial bit-length bounds for exact rational elimination

For an $m \times n$ rational matrix whose entries have numerators and denominators of absolute value at most $2^{\beta}$, fraction-free elimination computes its reduced row echelon form, rank, and (for a consistent system $Ax = b$) a rational solution, such that every intermediate integer has absolute value at most $(n!) \, 2^{n\beta'}$ for $\beta' = O(\beta + \log(mn))$; in particular all intermediate numbers have bit length polynomial in the input size, and Gaussian elimination over $\mathbb{Q}$ runs in polynomial time (Schrijver, Chapter 3).

## Proof sketch

Clear denominators row by row; Sylvester's identity identifies each intermediate value with a minor, and Hadamard's inequality bounds minors.

## Depends on

- [Fraction-free (Bareiss-Jordan) elimination](bareiss-fraction-free-elimination.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Sources

- A. Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
- E. H. Bareiss, "Sylvester's Identity and Multistep Integer-Preserving Gaussian Elimination", Mathematics of Computation 22(103), 1968.
