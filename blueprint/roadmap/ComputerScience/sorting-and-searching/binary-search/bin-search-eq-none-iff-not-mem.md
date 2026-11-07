# Binary search on a sorted array fails exactly on non-members

Let $A$ be an array with
entries in a linearly ordered type, sorted so that an earlier entry is never greater than a later
one, and let $k$ be an element of that type. Lean core's array binary search for $k$ over the
whole of $A$, with the strict order $<$ as comparison, returns no element if and only if $k$ is
not an entry of $A$.
