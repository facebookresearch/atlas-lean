# Representation check for the indexed interval tree

For an indexed interval tree, the
check returns true exactly when all of the following hold: at every node the cached height and size
agree with the values recomputed from its children's cached heights and sizes, and the cached
maximum high endpoint equals the largest of the node's own high endpoint and its children's cached
maxima; the tree is AVL-balanced (sibling heights differ by at most one) with exact stored heights;
the entry keys (low endpoint, identifier), ordered lexicographically, are strictly ordered as a
binary search tree and every stored interval has low endpoint at most its high endpoint; the
identifiers of the stored entries are pairwise distinct; the identifier index maps the identifier of
every stored entry to that entry's low endpoint; and every identifier and low endpoint paired by the
index belong to some stored entry.
