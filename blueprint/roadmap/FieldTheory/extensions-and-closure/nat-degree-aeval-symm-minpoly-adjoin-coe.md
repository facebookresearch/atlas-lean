# Transcendental coeff bound

Bound on the degree of a polynomial representing a minimal-polynomial
coefficient over a transcendental adjunction.

Let `x` be a nonzero transcendental element of a field extension `F / L`,
let `f` be integral over `L[x]`, and suppose `f / x ^ m` lies in every
valuation subring of `F` that contains `L` but not `x`. If a polynomial
`c` over `L` evaluates at `x` to the `j`-th coefficient of the minimal
polynomial of `f` over `L[x]`, then the degree of `c` is at most
`(natDegree (minpoly L[x] f) - j) * m`.
