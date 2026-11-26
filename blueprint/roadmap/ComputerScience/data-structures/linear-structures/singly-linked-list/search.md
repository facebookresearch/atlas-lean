# Search in a singly-linked list

Given a node pool with $n$ cells, a head $h$ that is
either an identity in $\{0, \dots, n-1\}$ or NIL, and a target payload $t$, the search for $t$
from $h$ is fuel-bounded search for $t$ from $h$ with fuel $n$. It follows next pointers from
$h$ and returns the first visited identity whose node has payload $t$, returning nothing if it
reaches NIL or an unallocated cell first, or if $n$ steps run out.
