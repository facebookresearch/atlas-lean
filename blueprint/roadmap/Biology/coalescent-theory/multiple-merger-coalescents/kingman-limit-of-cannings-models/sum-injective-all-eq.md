# Counting samples of distinct children with a common parent

For every parent map `f : {0, …, N - 1} → {0, …, N - 1}` and every `m ∈ ℕ`, the number of injective
`g : {0, …, m} → {0, …, N - 1}` (ordered samples of `m + 1` distinct children) whose children all
have the same parent, `f (g 0) = f (g 1) = ⋯ = f (g m)`, is `∑_j (ν_j)_{m+1}`. Here
`ν_j = #{c | f c = j}` is the number of children of parent `j` and
`(ν)_{m+1} = ν (ν - 1) ⋯ (ν - m)`.
