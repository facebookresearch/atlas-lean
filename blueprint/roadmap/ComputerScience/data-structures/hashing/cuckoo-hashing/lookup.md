# Cuckoo hash table lookup

For a cuckoo hash table $T$ with hash functions $h_1$ and $h_2$ and a
key $k$, the lookup of $k$ in $T$ returns $v$ if slot $h_1(k)$ of the first table holds a pair
$(k, v)$; otherwise it returns $v$ if slot $h_2(k)$ of the second table holds a pair $(k, v)$;
otherwise it returns nothing. No other slot is examined.
