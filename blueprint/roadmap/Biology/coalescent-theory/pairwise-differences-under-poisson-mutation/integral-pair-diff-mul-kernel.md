# Conditional product moment of two pairwise differences

Given the genealogy, the counts on
the branches are independent Poisson with means `λ_b = (θ/2) ℓ_b`, so
`E[D_s D_{s'} | g] = (∑_{b ∈ path s} λ_b)(∑_{b ∈ path s'} λ_b) + ∑_{b ∈ path s ∩ path s'} λ_b`:
the Poisson variance of a shared branch adds to the product of the means.
