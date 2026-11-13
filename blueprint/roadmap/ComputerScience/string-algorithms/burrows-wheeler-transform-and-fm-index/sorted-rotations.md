# Sorted rotations of a sentinel-terminated text

The starting positions `0, …, |t|` of the rotations of `withSentinel t`, sorted by their
rotations in lexicographic order: row `r` of the Burrows–Wheeler matrix is
`(withSentinel t).rotate ((sortedRotations t)[r])`.
