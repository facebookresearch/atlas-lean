# Cuckoo hash insertion

Inserting a key $k$ with value $v$ into a cuckoo hash table with hash
functions $h_1$ and $h_2$, with fuel $n$, either returns a table or fails. If slot $h_1(k)$ of
the first table holds a binding for $k$, that slot is overwritten with $(k, v)$, and slot
$h_2(k)$ of the second table is cleared if it also holds a binding for $k$, so no stale
competing value remains. Otherwise, if slot $h_2(k)$ of the second table holds a binding for
$k$, that slot is overwritten with $(k, v)$. Otherwise the eviction loop runs on $(k, v)$,
starting with the first table, with fuel $n$, and its result is returned. Failure, when the
loop exhausts its fuel, models the rehash trigger of the classical algorithm.
