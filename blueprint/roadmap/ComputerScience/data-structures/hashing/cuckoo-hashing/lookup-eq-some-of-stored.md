# Cuckoo lookup finds every stored binding

Let $T$ be a cuckoo hash table that satisfies
the placement invariant and is key-deterministic. For every key $k$ and value $v$, if the
binding $k \mapsto v$ is stored in $T$, then looking up $k$ in $T$ returns $v$.
