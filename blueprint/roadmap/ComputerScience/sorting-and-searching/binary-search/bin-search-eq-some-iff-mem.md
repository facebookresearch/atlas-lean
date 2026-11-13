# Binary search on a sorted array finds exactly its members

Let $A$ be an array with entries
in a linearly ordered type, sorted so that an earlier entry is never greater than a later one, and
let $k$ and $a$ be elements of that type. Lean core's array binary search for $k$ over the whole of
$A$, with the strict order $<$ as comparison, returns $a$ if and only if $a = k$ and $k$ is an
entry of $A$.
