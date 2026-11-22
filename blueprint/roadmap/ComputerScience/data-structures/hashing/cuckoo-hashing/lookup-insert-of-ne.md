# Cuckoo insertion leaves lookups of other keys unchanged

Let $T$ be a cuckoo hash table with
hash functions $h_1$ and $h_2$ that satisfies the placement invariant and stores each key with at
most one value. If inserting (or replacing) the binding $k \mapsto v$ in $T$ with fuel $f$ succeeds
and returns the table $T'$, then for every key $k' \ne k$, looking up $k'$ in $T'$ gives the same
result as looking up $k'$ in $T$: either both return nothing or both return the same value.
