# Insertion into an LRU cache

Putting the binding $(k, v)$ into an LRU cache of capacity $c$
removes any entry with key $k$, places $(k, v)$ at the front as the most recently used entry,
and then keeps only the first $c$ entries, so the least recently used entries beyond the
capacity are evicted.
