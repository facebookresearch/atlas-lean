# Ordinary kriging is unbiased for observations with a common mean

Let the observations `Z_i`, for `i` in a finite set of sites, be integrable random variables on a
probability space, all with the same expectation `μ`. Let the weights `λ_i` solve the ordinary
kriging system for a real matrix `C` (in kriging, the covariances between sites), a vector `c`
and a real multiplier `m`: `∑_j C_ij λ_j + m = c_i` for every site `i`, and `∑_i λ_i = 1`. Then
the kriging estimator `∑_i λ_i Z_i` has expectation `μ`. Unbiasedness follows from the constraint
`∑_i λ_i = 1` alone; the covariance equations play no part in it.
