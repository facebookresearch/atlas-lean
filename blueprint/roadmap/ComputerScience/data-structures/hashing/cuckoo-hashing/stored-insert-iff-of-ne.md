# Cuckoo insertion preserves the bindings of other keys

Let $T$ be a cuckoo hash table with hash
functions $h_1$ and $h_2$ that satisfies the placement invariant. Suppose inserting (or replacing)
the binding $k \mapsto v$ in $T$ with fuel $f$ succeeds and returns the table $T'$. Then for every
key $k' \ne k$ and every value $v'$, the binding $k' \mapsto v'$ is stored in $T'$ if and only if
it is stored in $T$.
