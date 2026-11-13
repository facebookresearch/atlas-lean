# Fuel-bounded search in a singly-linked list

Given a node pool with $n$ cells, a target
payload $t$, a fuel $f \in \mathbb{N}$ and a start $h$ that is either an identity in
$\{0, \dots, n-1\}$ or NIL, fuel-bounded search for $t$ from $h$ with fuel $f$ returns nothing
if $f = 0$ or $h$ is NIL. Otherwise $h$ is an identity $i$: the search returns nothing if cell
$i$ is unallocated, returns $i$ if the node in cell $i$ has payload $t$, and otherwise continues
from the next pointer of that node with fuel $f - 1$.
