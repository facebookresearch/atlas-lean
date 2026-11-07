# Access preserves validity

If a link-cut tree state $s$ is valid, then for every vertex
$x$ the state obtained from $s$ by accessing $x$ is again valid.

The new preferred edges are the retained off-path edges together with the edges of the accessed
root path; the two groups have disjoint parent endpoints (off versus on the path), so
duplicate-freeness and the at-most-one-preferred-child condition carry over.
