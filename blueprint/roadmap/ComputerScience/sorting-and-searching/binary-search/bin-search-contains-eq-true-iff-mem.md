# Binary search membership test on a sorted array is correct

Let $A$ be an array with
entries in a linearly ordered type, sorted so that an earlier entry is never greater than a later
one, and let $k$ be an element of that type. Lean core's Boolean binary search membership test
for $k$ over the whole of $A$, with the strict order $<$ as comparison, returns true if and only
if $k$ is an entry of $A$.
