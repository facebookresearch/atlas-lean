# Soundness of cuckoo lookup

Let $T$ be a cuckoo hash table with hash functions $h_1$ and $h_2$,
let $k$ be a key and $v$ a value. If looking up $k$ in $T$ returns $v$, then the binding
$k \mapsto v$ is stored in some slot of the first or the second table of $T$.
