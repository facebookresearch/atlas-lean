# Insertion into an indexed minimum queue

Let $W$ be a linearly ordered type and let
$W \cup \{\top\}$ be $W$ with a new greatest element $\top$ adjoined. Costs are counted as five
event counts: comparisons, swaps, reads of the position vector, writes to the position vector,
and entry appends, pops or replacements. Given an indexed minimum queue $q$ over the identities
$0, \dots, n-1$ with keys in $W \cup \{\top\}$, whose heap entries (pairs of a key and an
identity) are ordered lexicographically, first by key and then by identity, an identity $v < n$
and a key $k \in W \cup \{\top\}$, insertion fails (returns nothing) when the position vector of
$q$ assigns an index to $v$, at the cost of one position read. Otherwise it appends the entry
$(k, v)$ at the end of the heap, sets the position of $v$ to that slot, and sifts the entry up:
while it is not at the root and is smaller than its parent, it is swapped with its parent and
the positions of both swapped identities are updated. It returns the resulting queue, at the
cost of one position read, one position write and one entry append, plus one comparison for
each comparison with a parent and one swap and two position writes for each swap.
