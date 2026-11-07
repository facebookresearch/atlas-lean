# Operation cost counters for interval trees

A cost record for the interval tree consists
of seven natural-number counters, each defaulting to $0$: node visits, key comparisons, endpoint
comparisons, cached-maximum reads, cache writes, rotations, and identifier-index operations.

The cached-maximum counter is deliberately narrow: it counts only the reads made by search
pruning, one per visited node where the left subtree's cached maximum decides the descent. Node
construction, rebalancing and the rotations read cached heights, sizes and maxima while rebuilding
nodes; those reads are not counted separately, and maintenance work is reported through the cache
write, rotation and remaining counters instead.
