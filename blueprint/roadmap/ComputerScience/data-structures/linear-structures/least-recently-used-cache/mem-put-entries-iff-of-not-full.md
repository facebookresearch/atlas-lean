# Insertion without eviction

Let an LRU cache of capacity $c$ hold fewer than $c$
entries or already store a binding for the key $k$, and let $v$ be a value. Then a key-value
pair $p$ is stored in the cache after putting the binding $(k, v)$ if and only if $p = (k, v)$,
or $p$ was stored before and the key of $p$ differs from $k$.
