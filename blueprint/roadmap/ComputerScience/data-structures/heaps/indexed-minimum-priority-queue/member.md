# Membership test in an indexed minimum queue

Costs are counted as five event counts:
comparisons, swaps, reads of the position vector, writes to the position vector, and entry
appends, pops or replacements. For an indexed minimum queue $q$ over the identities
$0, \dots, n-1$ and an identity $v < n$, the membership test returns true exactly when the
position vector of $q$ assigns an index to $v$, and its cost is one position read and no other
event.
