# Totally positive matrices

A real matrix $M$ whose rows and columns are indexed by linearly ordered sets is totally positive (has positive minors) when every square submatrix with rows and columns in increasing order has positive determinant; it is totally nonnegative when all these minors are nonnegative.

## Idea

Total positivity is the strongest positivity condition on a matrix: not only the entries but every minor is positive. Examples of totally positive matrices are Vandermonde matrices with increasing positive nodes and the matrices $(e^{x_i y_j})$ for increasing $x$ and $y$; many matrices from combinatorics, such as Pascal's triangle, are totally nonnegative without being totally positive. A finite square totally positive matrix has distinct positive eigenvalues, and totally positive matrices diminish sign changes, which is why they matter in approximation theory, statistics and the theory of oscillating systems. For an $n \times n$ matrix, checking all minors is not necessary: by the Gasca–Peña criterion it suffices to check the $n^2$ initial minors, the contiguous minors that touch the first row or the first column.

## Statements

- [Matrices with positive minors](has-positive-minors.md)
- [Matrices with nonnegative minors](has-nonnegative-minors.md): totally nonnegative matrices
- [Nonnegative minors and total nonnegativity of square matrices](has-nonnegative-minors-iff-is-totally-no.md): two forms of total nonnegativity agree for square matrices
- [Entries of a matrix with positive minors are positive](entry-pos.md): the entries of a totally positive matrix are positive
- [Gasca–Peña criterion for total positivity](has-positive-minors-iff-initial-minors-p.md): the Gasca–Peña criterion by initial minors
