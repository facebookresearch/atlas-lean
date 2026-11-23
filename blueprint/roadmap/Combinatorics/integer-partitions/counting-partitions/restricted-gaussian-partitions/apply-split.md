# Split replacement in a dimension list

For natural numbers $q, a, b, c$ and a list $l$ of
natural numbers, the split replacement is defined exactly when $l$ has at least $c$ entries equal
to $a + b$. It removes the last $c$ entries of $l$ equal to $a + b$ and, at the position of the
first of these removed entries, inserts $c$ copies of $a$ followed by $c q^a$ copies of $b$; the
entries of $l$ before that position stay in front, and the entries after it that were not removed
follow in their original order. For $c = 0$ the list is unchanged.

No sorting is performed.
