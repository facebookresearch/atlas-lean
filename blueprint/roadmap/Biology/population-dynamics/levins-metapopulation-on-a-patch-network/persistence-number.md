# Persistence number of a patch network

For a finite set `ι` of patches, a real matrix `C` and real rates `e`, the persistence number is
`R₀ = ρ(C diag(e)⁻¹)`, the spectral radius (the largest modulus of a complex eigenvalue) of the
next-generation matrix with new colonizations `F = C` and losses `V = diag(e)`. When every
`e_j ≠ 0`, `C diag(e)⁻¹` has entries `C_ij / e_j`, for `C_ij ≥ 0` and `e_j > 0` the expected number
of colonizations of patch `i` by one population on patch `j` during its lifetime. When some
`e_j = 0`, the matrix `diag(e)` is singular, its inverse is taken to be the zero matrix, and
`R₀ = 0`; with no patches, `R₀ = 0`.
