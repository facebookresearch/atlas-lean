# Open-addressing lookup succeeds exactly on stored keys

Let $T$ be a valid open-addressing
hash table and $k$ a key. Looking up $k$ in $T$ returns a value if and only if $T$ stores a
binding $k \mapsto v$ for some value $v$.

This membership characterization is used in place of a finite-map abstraction of the table.
