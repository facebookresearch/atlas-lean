# Singular value decomposition of a complex matrix

Rectangular complex singular value decomposition: every complex `m × n` matrix
factors as `U * Σ * Vᴴ` with `U` and `V` unitary and `Σ` rectangular diagonal
with nonnegative entries; the singular values beyond the first `min m n`
(indices `j` with `m ≤ j.val`) are zero.

Proof: Apply the spectral theorem to `AᴴA`, normalize the images of the
eigenvectors with positive eigenvalues, and extend them to an orthonormal basis
of the codomain, as in the proof of S. Axler, Linear Algebra Done Right,
4th ed., 7.70, and the matrix form that follows it (Section 7E).

## Sources

- S. Axler, Linear Algebra Done Right, 4th ed., Section 7E; G. H. Golub and C. F. Van Loan, Matrix Computations, 4th ed., Johns Hopkins University Press (2013), Theorem 2.4.1.
