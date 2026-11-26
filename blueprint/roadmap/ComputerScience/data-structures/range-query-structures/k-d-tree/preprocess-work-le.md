# Preprocessing work for a planar leaf kd-tree

On any input list of length $n$, the
work of both presorts, rank indexing and all recursive median splits together is at most
$7 n\lceil\log_2 n\rceil + 12n + 2$ (the ceiling log at zero is zero).
