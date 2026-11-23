# Split-returning insertion into a B-tree subtree

For minimum degree $t$ and a key $x$,
insertion of $x$ into a tree returns an insertion result and is defined by recursion. At a leaf
with key list $K$, it is leaf insertion of $x$ into $K$. At an internal node, the separator list
and the child list are scanned together from the left. If $x$ is smaller than the current
separator, or no separator is left but a child is, $x$ is inserted into the current child. If $x$
is larger than the current separator, the scan moves on to the next separator and child. If $x$
equals the current separator, or no child is left, the remaining lists are kept unchanged. When
the child that received $x$ returns a single tree, that tree replaces the child; when it returns
two trees $\ell$, $r$ with a median $m$, the child is replaced by $\ell$ and $r$ with $m$ inserted
as a separator between them. The rebuilt separator and child lists are then turned into a node by
the internal-node rebuilding step: kept as one node if there are at most $2t - 1$ separators, and
split otherwise.
