# Critical probability of bond percolation on the hypercubic lattice

The critical probability `p_c(d) = sup {p ∈ [0, 1] : θ_d(p) = 0}` of bond percolation on `ℤ^d`.

See also `MathlibExt.Probability.ProductBondPercolation.criticalProb`, which defines the critical
point of a general countable graph through the event that *some* infinite cluster exists; the two
agree for `ℤ^d` by translation invariance, but that identification is not proved here.
