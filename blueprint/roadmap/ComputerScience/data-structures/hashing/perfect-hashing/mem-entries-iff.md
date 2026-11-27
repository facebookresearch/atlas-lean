# Entries of a perfect hash table are its stored bindings

For every two-level perfect hash
table, every key $k$ and every value $v$, the pair $(k, v)$ belongs to the list of entries of the
table (the contents of its occupied secondary slots, bucket by bucket) if and only if some
secondary slot of the table holds the binding $(k, v)$.
