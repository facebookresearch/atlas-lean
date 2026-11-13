# Additivity of the LogDet distance along a path

**Additivity of the LogDet distance along a path** (Steel 1994; Lockhart et al. 1994):
for a Markov chain `v₀ → v₁ → ⋯ → v_n` along a path, with positive initial distribution `p`
and nonnegative nonsingular transition matrices `M i` with unit row sums, the LogDet distance
between the ends is the sum of the distances of consecutive vertices. The joint distribution of
`v₀, v_n` is `Π_{v₀} M 0 ⋯ M (n - 1)`, and that of `v_i, v_{i+1}` is `Π_{v_i} M i`, where `v_i`
has distribution `p M 0 ⋯ M (i - 1)`. Under the general Markov model on a tree with positive
marginals and nonsingular matrices, the states along any path form such a chain once the model
is rooted at one end of the path.
