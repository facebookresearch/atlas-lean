# Recompute

Recompute a root from the current node `cur` at position `i` of a level with `n` nodes and the
remaining path `p`, for `k` levels. An odd position hashes the next path entry on the left; an
even position with a right neighbour hashes it on the right; an even last position is promoted
and consumes nothing. The path must be used up exactly.
