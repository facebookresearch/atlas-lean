# Euler's homogeneous-function identity for entropy

Euler homogeneous-function identity (differential form): differentiating
`S(tU, tV, tN) = t * S(U, V, N)` at `t = 1` gives
`SU*U + SV*V + ∑ SNᵢNᵢ = S`. Uses homogeneity `h_homog` and the chain rule
`hasDerivAt_comp_curve` along the ray.
