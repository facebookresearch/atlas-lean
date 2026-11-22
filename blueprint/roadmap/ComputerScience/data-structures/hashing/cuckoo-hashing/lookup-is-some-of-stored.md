# Cuckoo lookup finds every stored key

Let $T$ be a cuckoo hash table with hash functions $h_1$
and $h_2$ that satisfies the placement invariant, and let $k$ be a key and $v$ a value. If the
binding $k \mapsto v$ is stored in some slot of either table of $T$, then looking up $k$ in $T$
returns some value.

The returned value may differ from $v$ when $k$ is stored with two different values; when $T$
stores each key with at most one value, it is $v$.
