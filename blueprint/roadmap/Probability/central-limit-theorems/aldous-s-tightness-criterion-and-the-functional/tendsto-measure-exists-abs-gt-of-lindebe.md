# Lindeberg implies asymptotically negligible jumps

Assume `∀ n i, Measurable (ξ n i)` and `∀ n i, MemLp (ξ n i) 2 μ`.

Under the (unconditional) Lindeberg
condition `LindebergConditionTriangular`, the largest increment of row `n` tends to `0` in
probability: by the union bound and Chebyshev's inequality,
`P(max_{i<n} |ξ n i| > ε) ≤ ε⁻² ∑_{i<n} E[ξ n i² 1{|ξ n i| > ε}]`.
