# Cuckoo lookup finds exactly the stored bindings

Let $T$ be a cuckoo hash table that
satisfies the placement invariant and is key-deterministic. For every key $k$ and value $v$,
looking up $k$ in $T$ returns $v$ if and only if the binding $k \mapsto v$ is stored in $T$.
