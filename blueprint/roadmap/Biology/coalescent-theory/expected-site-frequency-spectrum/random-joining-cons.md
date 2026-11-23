# Random Joining cons

If `blockPairs b.length` is nonempty, `randomJoining (m + 1) b (b' :: rest)` is `0` unless
`b' = b`, and for `b' = b` it is the average over `p ∈ blockPairs b.length` of
`randomJoining m (mergeBlocks b p.1 p.2) rest`.
