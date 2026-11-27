# Evaluation rules for point updates

Over an additive monoid, an update at a natural-number
index $i$ with replacement value $y$ leaves the empty tree unchanged and replaces a
leaf's value with $y$ exactly when the local index is zero. At an internal node it calls
just the left child at $i$ if $i\lt m$, otherwise just the right child at $i-m$, where $m$
is the left size and subtraction is truncated. The trace records the selected child.
The result retains the other child and the cached size, and caches the new left aggregate
plus the new right aggregate, in that order.
