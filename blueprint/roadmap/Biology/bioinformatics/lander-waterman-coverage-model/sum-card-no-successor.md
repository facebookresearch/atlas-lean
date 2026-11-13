# Count of no-successor reads (exact)

For `L ≤ G`, summed over the
reads, the number of start tuples in which read `j` has no successor is
`N * G * (G - (L - 1)) ^ (N - 1)`. This counts no-successor reads, not island ends:
a start tuple can have several no-successor reads in one island.
