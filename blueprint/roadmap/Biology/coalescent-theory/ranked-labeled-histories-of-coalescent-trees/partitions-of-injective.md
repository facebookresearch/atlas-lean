# The ancestral partitions determine the ranked labeled history

For every sample size
`n`, `partitionsOf` is injective: two ranked labeled histories with the same sequence of
ancestral partitions are equal. At each step the blocks of a partition that are missing from
the next one are exactly the two blocks that merged, so equal partition sequences give equal
merged pairs at every step.
