# Cuckoo lookup returns an inserted value

Let $T$ be a cuckoo hash table with hash functions
$h_1$ and $h_2$ that satisfies the placement invariant and stores each key with at most one value.
If inserting (or replacing) the binding $k \mapsto v$ in $T$ with fuel $f$ succeeds and returns the
table $T'$, then looking up $k$ in $T'$ returns $v$.
