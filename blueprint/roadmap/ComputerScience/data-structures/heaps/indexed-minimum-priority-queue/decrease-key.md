# Decrease-key in an indexed minimum queue

Let $W$ be a linearly ordered type and let
$W \cup \{\top\}$ be $W$ with a new greatest element $\top$ adjoined. Costs are counted as five
event counts: comparisons, swaps, reads of the position vector, writes to the position vector,
and entry appends, pops or replacements. Given an indexed minimum queue $q$ over the identities
$0, \dots, n-1$ with keys in $W \cup \{\top\}$, whose heap entries (pairs of a key and an
identity) are ordered lexicographically, first by key and then by identity, an identity $v < n$
and a finite key $k \in W$, decrease-key fails (returns nothing) when the position vector of $q$
assigns no index to $v$, at the cost of one position read, and when $k$ is not strictly smaller
than the current key of $v$, at the cost of one position read and one comparison. Otherwise it
replaces the entry of $v$ by $(k, v)$ in the same slot and sifts it up: while it is not at the
root and is smaller than its parent, it is swapped with its parent and the positions of both
swapped identities are updated. It returns the resulting queue, at the cost of one position
read, one comparison and one entry replacement, plus one comparison for each comparison with a
parent and one swap and two position writes for each swap.
