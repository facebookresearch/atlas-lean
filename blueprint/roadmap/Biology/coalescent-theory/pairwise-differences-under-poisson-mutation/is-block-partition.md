# Block partition of the sample with gene positions

For a natural number `n`, let `B₀, …, B_{r-1}` be a list of subsets of the sample
`{0, …, n - 1}` and `pos` a map from the sample to the natural numbers. The list is a block
partition with positions `pos` when every gene `a` satisfies `pos a < r` and, for every `j < r`,
`a ∈ B_j` if and only if `j = pos a`: each gene lies in the block at position `pos a` and in no
other. The blocks are then pairwise disjoint and cover the sample, and `pos` is determined by the
list. Empty blocks are allowed.
