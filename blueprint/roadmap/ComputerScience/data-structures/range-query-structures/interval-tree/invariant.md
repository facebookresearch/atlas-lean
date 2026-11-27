# Representation invariant of an indexed interval tree

An indexed interval tree $T$
satisfies the representation invariant when its root tree has exact cached metadata (heights,
sizes, and attained maximum high endpoints), is strictly ordered by the composite key (low
endpoint, then identifier), is AVL balanced with exact stored heights, and stores only valid
intervals; the identifiers of the stored entries are pairwise distinct; the identifier index maps
the identifier of every stored entry to that entry's low endpoint; and every pair $(i, \ell)$ in
the identifier index is the identifier and low endpoint of some stored entry.

The ordering of low endpoints used by search follows from the strict key ordering.
