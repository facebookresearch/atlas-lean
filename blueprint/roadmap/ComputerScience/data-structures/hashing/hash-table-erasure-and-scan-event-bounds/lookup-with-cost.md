# Lookup With Cost

For a hash table with $m$ buckets and hash function $h$, the selected chain of a key $k$ is the bucket at index $h(k) \bmod m$; keys need not lie in their selected bucket unless the table is valid. A scan of the selected chain charges one event per entry compared with $k$ until the first entry with key $k$, counting that successful comparison, or one terminal event at the end of the chain when no entry has key $k$. The costed lookup of $k$ returns the value of the first entry with key $k$ in the selected chain, if any, together with the number of scan events.
