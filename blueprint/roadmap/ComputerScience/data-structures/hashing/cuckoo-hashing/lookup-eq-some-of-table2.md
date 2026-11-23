# Cuckoo lookup finds a key in its second-table slot

Let $T$ be a cuckoo hash table with hash
functions $h_1$ and $h_2$, let $k$ be a key and $v$ a value. If slot $h_2(k)$ of the second table
of $T$ holds the pair $(k, v)$ and slot $h_1(k)$ of the first table of $T$ holds no pair whose key
is $k$, then looking up $k$ in $T$ returns $v$.
