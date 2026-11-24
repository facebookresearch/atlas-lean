# Bound on the number of four-child samples forming two coalescing pairs

For every parent map `f : {0, …, N - 1} → {0, …, N - 1}`, the number of injective
`g : {0, 1, 2, 3} → {0, …, N - 1}` (ordered samples of four distinct children) with
`f (g 0) = f (g 1)` and `f (g 2) = f (g 3)` is at most `X²`, where `X = ∑_j ν_j (ν_j - 1)` is the
[pair count](pair-count.md) and `ν_j` the number of children of parent `j`. The two common parents
may coincide.
