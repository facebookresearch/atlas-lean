# Sum of the visited Fenwick prefix blocks

For a list $a$ over any additive commutative
monoid and any requested length $k$, sum the stored block sums of $a$ at the one-indexed
endpoints visited by the prefix walk of array length $|a|$. This equals the sum of the first
$\min(k,|a|)$ entries of $a$, including $0$ for an empty prefix and the whole sum for
requests beyond the end.
