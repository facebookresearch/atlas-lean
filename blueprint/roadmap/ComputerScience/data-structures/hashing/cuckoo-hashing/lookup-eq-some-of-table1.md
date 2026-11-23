# Cuckoo lookup finds a key in its first-table slot

Let $T$ be a cuckoo hash table with hash
functions $h_1$ and $h_2$, let $k$ be a key and $v$ a value. If slot $h_1(k)$ of the first table of
$T$ holds the pair $(k, v)$, then looking up $k$ in $T$ returns $v$.
