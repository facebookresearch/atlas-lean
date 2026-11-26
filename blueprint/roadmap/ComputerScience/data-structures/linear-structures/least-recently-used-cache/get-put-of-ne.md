# A put without eviction preserves lookups of other keys

Let $C$ be an LRU cache of
capacity $c$ that holds fewer than $c$ entries or already stores the key $k$. Then for every
key $k' \ne k$ and every value $v$, looking up $k'$ in the cache obtained by putting the binding
$(k, v)$ into $C$ returns the same optional value as looking up $k'$ in $C$.
